/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import SimplexMellin.Bridge
public import ToMathlib.Analysis.SpecialFunctions.Gamma
public import ToMathlib.Analysis.Integral.FunSplitAt
public import Mathlib.MeasureTheory.Function.JacobianOneDim

/-!
# Log-ratio coordinates on the simplex

Fix an index `i₀`. The open standard simplex is parametrized by `w : {j // j ≠ i₀} → ℝ` through

`u(w) = e^(w̃) / ∑ e^(w̃)`, `w̃ i₀ = 0`, `w̃ j = w j`,

so that `w j = log (u j / u i₀)`. With `Z(w) = ∑ i, e^(w̃ i) = 1 + ∑ j, e^(w j)`, the change of
variables reads

`∫_Δ f(u) du = ∫ (∏ i, u(w) i) f(u(w)) dw`,

for `f` continuous on the simplex, with `∏ i, u(w) i = e^(∑ w) Z(w)^(-card ι)`.
More generally, positive complex Mellin parameters allow singular monomial densities
and arbitrary continuous boundary kernels in the corresponding weighted identity.

The proof avoids computing the Jacobian of `w ↦ u(w)` directly. It evaluates the multivariable
Mellin transform of `e^(-∑ x) f(x / ∑ x)` at `b = 𝟙` in two ways: by the Mellin bridge it is
`Γ(card ι) ∫_Δ f`; in exponential coordinates `y = τ 𝟙 + w̃` (a shear of the coordinates that split
off `y i₀ = τ`) the integral over `τ` is `Γ(card ι) Z(w)^(-card ι)`.

## Main definitions

* `Dirichlet.logRatioPoint`: the point `u(w)` of the simplex.

## Main results

* `Dirichlet.integral_exp_mul_exp_neg_mul_exp`: `∫ e^(k τ) e^(-Z e^τ) dτ = Z^(-k) Γ(k)`.
* `Dirichlet.prodGamma_regDirichletIntegral_eq_integral_logRatio`: the positive-parameter identity.
* `Dirichlet.integral_stdSimplex_eq_integral_logRatio`: its continuous-integrand specialization.
-/

open Complex MeasureTheory Set
open MvMellin
open scoped Topology

@[expose] public noncomputable section

namespace Dirichlet

/-- **The Gamma integral in exponential coordinates.** For `Z > 0` and `Re a > 0`,
`∫ e^(a τ) e^(-Z e^τ) dτ = Z^(-a) Γ(a)`. -/
theorem integral_exp_mul_exp_neg_mul_exp {a : ℂ} (ha : 0 < a.re) {Z : ℝ} (hZ : 0 < Z) :
    ∫ τ : ℝ, Complex.exp (a * τ) * ((Real.exp (-(Z * Real.exp τ)) : ℝ) : ℂ) =
      (Z : ℂ) ^ (-a) * Gamma a := by
  have h := Complex.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos ha (w := (Z : ℂ)) (by simpa)
  rw [← h, show Ioi (0 : ℝ) = Real.exp '' univ by rw [Set.image_univ, Real.range_exp],
    integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    Measure.restrict_univ]
  refine integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only [abs_of_pos (Real.exp_pos τ), real_smul]
  rw [ofReal_exp_cpow, Complex.ofReal_exp, ← mul_assoc, ← Complex.exp_add]
  push_cast
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  ring

open scoped Classical

variable {ι : Type*} [Fintype ι] (i₀ : ι)

/-- Extension of `w` by `0` at `i₀`. -/
def logRatioExt (w : {j : ι // j ≠ i₀} → ℝ) : ι → ℝ := fun i => if h : i = i₀ then 0 else w ⟨i, h⟩

/-- The normalizing sum `Z(w) = ∑ i, e^(w̃ i) = 1 + ∑ j, e^(w j)`. -/
def logRatioZ (w : {j : ι // j ≠ i₀} → ℝ) : ℝ := ∑ i, piExp (logRatioExt i₀ w) i

/-- The point of the simplex with log-ratio coordinates `w` relative to `i₀`. -/
def logRatioPoint (w : {j : ι // j ≠ i₀} → ℝ) : ι → ℝ :=
  (logRatioZ i₀ w)⁻¹ • piExp (logRatioExt i₀ w)

/-- The normalizing sum is positive. -/
theorem logRatioZ_pos (w : {j : ι // j ≠ i₀} → ℝ) : 0 < logRatioZ i₀ w :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨i₀, Finset.mem_univ _⟩

/-- The log-ratio point lies in the simplex. -/
theorem logRatioPoint_mem (w : {j : ι // j ≠ i₀} → ℝ) :
    logRatioPoint i₀ w ∈ Convexity.StdSimplex.coordinateSet ℝ ι :=
  have : Nonempty ι := ⟨i₀⟩
  inv_sum_smul_mem_coordinateSet fun _ _ => Real.exp_pos _

/-- The sum of the extended coordinates is the sum of the log-ratio coordinates. -/
theorem sum_logRatioExt (w : {j : ι // j ≠ i₀} → ℝ) : ∑ i, logRatioExt i₀ w i = ∑ j, w j := by
  rw [Fintype.sum_eq_add_sum_subtype_ne _ i₀]
  simp only [logRatioExt, dite_true, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [j.2]

/-- The product of the coordinates of the log-ratio point. -/
theorem prod_logRatioPoint (w : {j : ι // j ≠ i₀} → ℝ) :
    ∏ i, logRatioPoint i₀ w i = Real.exp (∑ j, w j) * (logRatioZ i₀ w)⁻¹ ^ Fintype.card ι := by
  simp only [logRatioPoint, Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, piExp]
  rw [← Real.exp_sum, sum_logRatioExt, mul_comm]

/-- The shear `(τ, w) ↦ (τ, w + τ 𝟙)` as a measurable equivalence. -/
def logRatioShear : ℝ × ({j : ι // j ≠ i₀} → ℝ) ≃ᵐ ℝ × ({j : ι // j ≠ i₀} → ℝ) where
  toFun p := (p.1, p.2 + fun _ => p.1)
  invFun p := (p.1, p.2 - fun _ => p.1)
  left_inv p := by simp
  right_inv p := by simp
  measurable_toFun := measurable_fst.prodMk
    (measurable_snd.add (measurable_pi_iff.mpr fun _ => measurable_fst))
  measurable_invFun := measurable_fst.prodMk
    (measurable_snd.sub (measurable_pi_iff.mpr fun _ => measurable_fst))

/-- The shear preserves Lebesgue measure. -/
theorem measurePreserving_logRatioShear :
    MeasurePreserving (logRatioShear i₀) ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := by
  have h := (MeasurePreserving.id (volume : Measure ℝ)).skew_product
    (g := fun (τ : ℝ) (w : {j : ι // j ≠ i₀} → ℝ) => w + fun _ => τ) (by fun_prop)
    (Filter.Eventually.of_forall fun τ => map_add_right_eq_self volume _)
  exact h

/-- Positive Mellin parameters give the log-ratio change of variables for every continuous
boundary kernel. The monomial density may be singular on the boundary. -/
theorem prodGamma_regDirichletIntegral_eq_integral_logRatio {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) {g : (ι → ℝ) → ℂ}
    (hg : ContinuousOn g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    (∏ i, Gamma (b i)) * regDirichletIntegral b g =
      ∫ w : {j : ι // j ≠ i₀} → ℝ,
        Complex.exp (∑ i, b i * (logRatioExt i₀ w i - Real.log (logRatioZ i₀ w))) *
          g (logRatioPoint i₀ w) := by
  have : Nonempty ι := ⟨i₀⟩
  have ha : 0 < (∑ i, b i).re := by
    rw [re_sum]
    exact Finset.sum_pos (fun i _ => hb i) Finset.univ_nonempty
  set φ : ℝ → ℂ := fun t => ((Real.exp (-t) : ℝ) : ℂ)
  set K : (ι → ℝ) → ℂ := fun x => φ (∑ i, x i) * g ((∑ i, x i)⁻¹ • x)
  set Φ : (ι → ℝ) → ℂ := fun y => Complex.exp (∑ i, b i * y i) * K (piExp y)
  have hB : mvMellin K b = Gamma (∑ i, b i) *
      ((∏ i, Gamma (b i)) * regDirichletIntegral b g) := mvMellin_exp_neg_mul_eq hb hg
  have hE : mvMellin K b = ∫ y, Φ y := by
    rw [mvMellin_eq_integral_exp]
    rfl
  have hφm : MellinConvergent φ (∑ i, b i) := by
    simpa [MellinConvergent, smul_eq_mul, mul_comm, φ] using Complex.GammaIntegral_convergent ha
  have hΦi : Integrable Φ := by
    exact (mvMellinConvergent_iff_integrable_exp K b).mp
      (mvMellinConvergent_radial_mul hb hg (by fun_prop) hφm)
  let T : ℝ × ({j : ι // j ≠ i₀} → ℝ) ≃ᵐ (ι → ℝ) :=
    (logRatioShear i₀).trans (Homeomorph.funSplitAt ℝ i₀).symm.toMeasurableEquiv
  have hT : MeasurePreserving T ((volume : Measure ℝ).prod volume) volume :=
    (MeasurePreserving.symm (Homeomorph.funSplitAt ℝ i₀).toMeasurableEquiv
      (volume_preserving_funSplitAt i₀)).comp (measurePreserving_logRatioShear i₀)
  have hΦT : Integrable (Φ ∘ T) ((volume : Measure ℝ).prod volume) := by
    rw [hT.integrable_comp_emb T.measurableEmbedding]
    exact hΦi
  have hsplit : ∫ y, Φ y = ∫ w : {j : ι // j ≠ i₀} → ℝ, ∫ τ : ℝ, Φ (T (τ, w)) := by
    rw [← hT.integral_comp' (g := Φ)]
    exact integral_prod_symm _ hΦT
  have hTy : ∀ τ w, T (τ, w) = (fun _ => τ) + logRatioExt i₀ w := by
    intro τ w
    funext i
    by_cases hi : i = i₀
    · subst hi; simp [T, logRatioShear, logRatioExt]
    · simp [T, logRatioShear, logRatioExt, hi, add_comm]
  have hinner : ∀ w : {j : ι // j ≠ i₀} → ℝ, ∫ τ : ℝ, Φ (T (τ, w)) =
      Gamma (∑ i, b i) * (Complex.exp
        (∑ i, b i * (logRatioExt i₀ w i - Real.log (logRatioZ i₀ w))) *
          g (logRatioPoint i₀ w)) := by
    intro w
    set Z := logRatioZ i₀ w
    have hZ := logRatioZ_pos i₀ w
    have hpt : ∀ τ : ℝ, Φ (T (τ, w)) =
        (Complex.exp (∑ i, b i * logRatioExt i₀ w i) * g (logRatioPoint i₀ w)) *
          (Complex.exp ((∑ i, b i) * τ) * ((Real.exp (-(Z * Real.exp τ)) : ℝ) : ℂ)) := by
      intro τ
      have hexp : piExp ((fun _ => τ) + logRatioExt i₀ w) =
          Real.exp τ • piExp (logRatioExt i₀ w) := by
        funext i; simp [piExp, Real.exp_add]
      have hS : ∑ i, piExp ((fun _ => τ) + logRatioExt i₀ w) i = Real.exp τ * Z := by
        rw [hexp]; simp [Z, logRatioZ, Finset.mul_sum]
      have hsumy : ∑ i, b i * (((fun _ => τ) + logRatioExt i₀ w : ι → ℝ) i : ℂ) =
          (∑ i, b i) * τ + ∑ i, b i * logRatioExt i₀ w i := by
        simp [mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      have hnorm : (∑ i, piExp ((fun _ => τ) + logRatioExt i₀ w) i)⁻¹ •
          piExp ((fun _ => τ) + logRatioExt i₀ w) = logRatioPoint i₀ w := by
        rw [hS, hexp, smul_smul, logRatioPoint]
        congr 1
        have := (Real.exp_pos τ).ne'
        field_simp
        exact div_self hZ.ne'
      simp only [Φ, K, φ, hTy]
      rw [hnorm, hsumy, hS, Complex.exp_add]
      ring_nf
    simp_rw [hpt]
    rw [MeasureTheory.integral_const_mul, integral_exp_mul_exp_neg_mul_exp ha hZ]
    have he : Complex.exp (∑ i, b i * logRatioExt i₀ w i) * (Z : ℂ) ^ (-(∑ i, b i)) =
        Complex.exp (∑ i, b i * (logRatioExt i₀ w i - Real.log Z)) := by
      rw [cpow_def_of_ne_zero (ofReal_ne_zero.mpr hZ.ne'), ← ofReal_log hZ.le,
        ← Complex.exp_add]
      congr 1
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
      ring
    rw [show (Complex.exp (∑ i, b i * logRatioExt i₀ w i) * g (logRatioPoint i₀ w)) *
        ((Z : ℂ) ^ (-(∑ i, b i)) * Gamma (∑ i, b i)) =
      Gamma (∑ i, b i) * ((Complex.exp (∑ i, b i * logRatioExt i₀ w i) *
        (Z : ℂ) ^ (-(∑ i, b i))) * g (logRatioPoint i₀ w)) by ring, he]
  have hall := hB.symm.trans (hE.trans hsplit)
  simp_rw [hinner, MeasureTheory.integral_const_mul] at hall
  exact mul_left_cancel₀ (Gamma_ne_zero_of_re_pos ha) hall

/-- **Change of variables to log-ratio coordinates.** For `f` continuous on the simplex,
`∫_Δ f(u) du = ∫ (∏ i, u(w) i) f(u(w)) dw` over `w : {j // j ≠ i₀} → ℝ`. -/
theorem integral_stdSimplex_eq_integral_logRatio {f : (ι → ℝ) → ℂ}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂Measure.stdSimplexMeasure =
      ∫ w : {j : ι // j ≠ i₀} → ℝ,
        ((∏ i, logRatioPoint i₀ w i : ℝ) : ℂ) * f (logRatioPoint i₀ w) := by
  have h := prodGamma_regDirichletIntegral_eq_integral_logRatio i₀
    (b := fun _ => 1) (fun _ => by simp) hf
  rw [regDirichletIntegral_eq_prod_inv_Gamma_mul] at h
  simp only [Gamma_one, Finset.prod_const_one, inv_one, one_mul, sub_self, cpow_zero] at h
  refine h.trans (integral_congr_ae (Filter.Eventually.of_forall fun w => ?_))
  dsimp only
  congr 1
  rw [Complex.exp_sum, ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [← ofReal_sub, ← Complex.ofReal_exp, Real.exp_sub,
    Real.exp_log (logRatioZ_pos i₀ w)]
  simp [logRatioPoint, piExp, div_eq_inv_mul]

end Dirichlet

end
