/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Mathlib.Analysis.MellinTransform
public import ToMathlib.Analysis.SpecialFunctions.Pow
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.Fourier.FourierTransform
public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# The multivariable Mellin transform

For a function `f` on the open positive orthant of `ℝ^ι` and complex exponents `s : ι → ℂ`, the
multivariable Mellin transform is

`mvMellin f s = ∫_{x > 0} (∏ i, x i ^ (s i - 1)) • f x dx`.

This is the multivariable companion of Mathlib's `mellin`. The substitution `x = exp y`
(coordinatewise) turns it into the integral of `exp (∑ i, s i * y i) • f (exp y)` over `ℝ^ι`, and
hence, on each vertical plane `Re s = c`, into a Fourier transform on `EuclideanSpace ℝ ι`.
For separable functions it is the product of one-variable Mellin transforms.

## Main definitions

* `mvMellin`: the multivariable Mellin transform.
* `MvMellinConvergent`: absolute convergence of the defining integral.

## Main results

* `mvMellin_eq_integral_exp`: the exponential change of variables.
* `mvMellinConvergent_iff_integrable_exp`: convergence in exponential coordinates.
* `mvMellin_eq_fourier`: the Fourier form on a vertical plane.
* `mvMellin_prod`: the transform of a separable function is a product of Mellin transforms.
* `mvMellin_exp_neg_sum`: the transform of `exp (-∑ i, x i)` is `∏ i, Γ(s i)`.

## Implementation notes

The definitions and proofs follow the one-variable `Mathlib.Analysis.MellinTransform` and
`Mathlib.Analysis.MellinInversion`.
-/

@[expose] public noncomputable section

open Real Complex Set MeasureTheory
open scoped FourierTransform

variable {ι : Type*} [Fintype ι] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The open positive orthant of `ℝ^ι`. -/
def posOrthant (ι : Type*) : Set (ι → ℝ) := univ.pi fun _ ↦ Ioi 0

/-- The open positive orthant is measurable. -/
theorem measurableSet_posOrthant : MeasurableSet (posOrthant ι) :=
  MeasurableSet.univ_pi fun _ ↦ measurableSet_Ioi

/-- The Mellin weight `∏ i, x i ^ (s i - 1)`. -/
def mvMellinWeight (s : ι → ℂ) (x : ι → ℝ) : ℂ := ∏ i, (x i : ℂ) ^ (s i - 1)

/-- The multivariable Mellin transform of `f` at the exponents `s`: the integral of
`∏ i, x i ^ (s i - 1) • f x` over the open positive orthant. -/
def mvMellin (f : (ι → ℝ) → E) (s : ι → ℂ) : E :=
  ∫ x in posOrthant ι, mvMellinWeight s x • f x

/-- The defining integral of the multivariable Mellin transform converges absolutely. -/
def MvMellinConvergent (f : (ι → ℝ) → E) (s : ι → ℂ) : Prop :=
  IntegrableOn (fun x ↦ mvMellinWeight s x • f x) (posOrthant ι)

/-- Coordinatewise exponential map from `ℝ^ι` onto the open positive orthant. -/
def piExp (y : ι → ℝ) : ι → ℝ := fun i ↦ Real.exp (y i)

omit [Fintype ι] in
/-- The coordinatewise exponential maps `ℝ^ι` onto the open positive orthant. -/
theorem piExp_image_univ : piExp '' univ = posOrthant ι := by
  ext x
  constructor
  · rintro ⟨y, -, rfl⟩ i -
    exact Real.exp_pos (y i)
  · intro hx
    refine ⟨fun i ↦ Real.log (x i), mem_univ _, ?_⟩
    funext i
    exact Real.exp_log (hx i (mem_univ i))

omit [Fintype ι] in
/-- The coordinatewise exponential is injective. -/
theorem piExp_injective : Function.Injective (piExp (ι := ι)) := fun _ _ h ↦
  funext fun i ↦ Real.exp_injective (congrFun h i)

/-- The derivative of the coordinatewise exponential: the diagonal map with entries
`exp (y i)`. -/
def piExpDeriv (y : ι → ℝ) : (ι → ℝ) →L[ℝ] (ι → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ Real.exp (y i) • ContinuousLinearMap.proj i

/-- The coordinatewise exponential has the diagonal derivative. -/
theorem hasFDerivAt_piExp (y : ι → ℝ) : HasFDerivAt piExp (piExpDeriv y) y := by
  refine hasFDerivAt_pi.mpr fun i ↦ ?_
  exact (Real.hasDerivAt_exp (y i)).comp_hasFDerivAt y
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i).hasFDerivAt

/-- The Jacobian of the coordinatewise exponential is `∏ i, exp (y i)`. -/
theorem det_piExpDeriv (y : ι → ℝ) : (piExpDeriv y).det = ∏ i, Real.exp (y i) := by
  classical
  have h : (piExpDeriv y : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) =
      Matrix.toLin' (Matrix.diagonal fun i ↦ Real.exp (y i)) := by
    ext v i
    simp [piExpDeriv, Matrix.mulVec_diagonal]
  rw [ContinuousLinearMap.det, h, LinearMap.det_toLin', Matrix.det_diagonal]

/-- The Mellin weight times the Jacobian, in exponential coordinates. -/
theorem abs_det_smul_mvMellinWeight_piExp (s : ι → ℂ) (y : ι → ℝ) :
    ((|(piExpDeriv y).det| : ℝ) : ℂ) * mvMellinWeight s (piExp y) =
      Complex.exp (∑ i, s i * y i) := by
  rw [det_piExpDeriv, abs_of_pos (Finset.prod_pos fun i _ ↦ Real.exp_pos (y i)),
    mvMellinWeight, Complex.exp_sum, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  simp only [piExp]
  rw [ofReal_exp_cpow, Complex.ofReal_exp, ← Complex.exp_add]
  ring_nf

/-- **The exponential change of variables.** The multivariable Mellin transform is the integral
over `ℝ^ι` of `exp (∑ i, s i * y i) • f (exp y)`. -/
theorem mvMellin_eq_integral_exp (f : (ι → ℝ) → E) (s : ι → ℂ) :
    mvMellin f s = ∫ y, Complex.exp (∑ i, s i * y i) • f (piExp y) := by
  rw [mvMellin, ← piExp_image_univ, integral_image_eq_integral_abs_det_fderiv_smul volume
    MeasurableSet.univ (fun y _ ↦ (hasFDerivAt_piExp y).hasFDerivWithinAt)
    piExp_injective.injOn, Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [← abs_det_smul_mvMellinWeight_piExp, ← smul_smul, Complex.coe_smul]

/-- **Convergence in exponential coordinates.** -/
theorem mvMellinConvergent_iff_integrable_exp (f : (ι → ℝ) → E) (s : ι → ℂ) :
    MvMellinConvergent f s ↔ Integrable fun y ↦ Complex.exp (∑ i, s i * y i) • f (piExp y) := by
  rw [MvMellinConvergent, ← piExp_image_univ,
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume MeasurableSet.univ
      (fun y _ ↦ (hasFDerivAt_piExp y).hasFDerivWithinAt) piExp_injective.injOn,
    integrableOn_univ]
  refine integrable_congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only
  rw [← abs_det_smul_mvMellinWeight_piExp, ← smul_smul, Complex.coe_smul]

/-- **The Fourier form.** On the vertical plane `Re s = c`, the multivariable Mellin transform is
the Fourier transform on `EuclideanSpace ℝ ι` of `y ↦ exp (⟨c, y⟩) • f (exp y)`, evaluated at
`-Im s / (2π)`. -/
theorem mvMellin_eq_fourier (f : (ι → ℝ) → E) (s : ι → ℂ) :
    mvMellin f s = 𝓕 (fun y : EuclideanSpace ℝ ι ↦
      Real.exp (∑ i, (s i).re * y i) • f (piExp y))
      (WithLp.toLp 2 fun i ↦ -(s i).im / (2 * π)) := by
  rw [mvMellin_eq_integral_exp, Real.fourier_eq',
    ← (PiLp.volume_preserving_toLp ι).integral_comp
      (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [← Complex.coe_smul, smul_smul]
  congr 1
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.mpr pi_ne_zero
  conv_lhs => rw [← re_add_im (s i)]
  field_simp
  ring

/-- **Separable functions.** The multivariable Mellin transform of `x ↦ ∏ i, f i (x i)` is the
product of the one-variable Mellin transforms. -/
theorem mvMellin_prod (f : ι → ℝ → ℂ) (s : ι → ℂ) :
    mvMellin (fun x ↦ ∏ i, f i (x i)) s = ∏ i, mellin (f i) (s i) := by
  rw [mvMellin, posOrthant, volume_pi, Measure.restrict_pi_pi]
  simp_rw [mvMellinWeight, smul_eq_mul, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun i (t : ℝ) ↦ (t : ℂ) ^ (s i - 1) * f i t)]
  rfl

/-- **The Gamma example.** The multivariable Mellin transform of `x ↦ ∏ i, exp (-x i)`, that is
of `exp (-∑ i, x i)` on the orthant, is `∏ i, Γ(s i)` when every `s i` has positive real part. -/
theorem mvMellin_exp_neg_sum {s : ι → ℂ} (hs : ∀ i, 0 < (s i).re) :
    mvMellin (fun x ↦ ∏ i, ((Real.exp (-x i) : ℝ) : ℂ)) s = ∏ i, Complex.Gamma (s i) := by
  rw [mvMellin_prod (fun _ t ↦ ((Real.exp (-t) : ℝ) : ℂ))]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Complex.Gamma_eq_integral (hs i), Complex.GammaIntegral_eq_mellin]
