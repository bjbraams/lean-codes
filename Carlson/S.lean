/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.RPolynomial.PowerSeries

public import Dirichlet.Average
public import Carlson.RPolynomial.Estimates
public import SeveralComplexVariables.LocallyUniform
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.Deriv.Pi

/-!
# Carlson's multivariate S-function

Carlson's `S(b,z)` is the Dirichlet average of the exponential function.  Section 5.8 of
[Carl77] defines it by an integral for Dirichlet parameters of positive real part.  Corollary
6.3-3 and formula (6.3-5) continue the regularized function `S(b,z) / Γ(∑ i, b i)` to all `b`.

This file separates the native integral from its continuation.  `regCarlsonSIntegral` and
`carlsonSIntegral` give the regularized and unregularized integral expressions.
`IsRegCarlsonSContinuation` specifies the global analytic object by entire dependence on `b`
and agreement with the native integral on `Complex.mvBetaConvergent`.

The series `regCarlsonSSeries` is the Taylor-series candidate corresponding to Carlson's
formula (6.3-5).  Establishing its convergence, analyticity, and agreement with the integral is
left to the subsequent analytic-continuation development; the definition itself makes none of
those claims.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, §§5.8 and 6.3,
  Academic Press, 1977.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonS

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The native regularized integral representing `S(b,z) / Γ(∑ i, b i)` when all Dirichlet
parameters have positive real part. -/
def regCarlsonSIntegral (b z : ι → ℂ) : ℂ :=
  regCarlsonDirichletAverage b z exp

/-- For each simplex point, the exponential Carlson kernel is entire in all `z` variables. -/
theorem analyticOnNhd_exp_carlsonAffineForm (u : ι → ℝ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ ↦ exp (carlsonAffineForm z u)) Set.univ := by
  intro z _
  apply analyticAt_cexp.comp
  unfold carlsonAffineForm
  apply Finset.analyticAt_fun_sum
  intro i _
  exact analyticAt_const.mul ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt z)

/-- Varying coordinate `i` of `z`, the derivative of the exponential Carlson kernel is the
kernel multiplied by the simplex coordinate `u i`. -/
theorem hasDerivAt_exp_carlsonAffineForm_update
    (z : ι → ℂ) (u : ι → ℝ) (i : ι) :
    HasDerivAt (fun w ↦ exp (carlsonAffineForm (Function.update z i w) u))
      ((u i : ℂ) * exp (carlsonAffineForm z u)) (z i) := by
  exact HasDerivAt.comp_carlsonAffineForm_update i
    (Complex.hasDerivAt_exp (carlsonAffineForm z u))

/-- Coordinate differentiation of the native regularized `S` integral.  This is the
specialization of Carlson's differentiation formula to the exponential kernel. -/
theorem hasDerivAt_regCarlsonSIntegral_update
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι) :
    HasDerivAt (fun w ↦ regCarlsonSIntegral b (Function.update z i w))
      (regDirichletIntegral b
        (fun u ↦ (u i : ℂ) * exp (carlsonAffineForm z u))) (z i) := by
  simpa only [regCarlsonSIntegral, Complex.deriv_exp] using
    hasDerivAt_regCarlsonDirichletAverage_update_of_analyticOnNhd
      isOpen_univ convex_univ (fun _ _ => analyticAt_cexp) hb
      (Set.subset_univ (Set.range z)) i

/-- Carlson's coordinate differentiation formula for the regularized native `S` integral:
differentiation in `z i` raises the corresponding Dirichlet parameter. -/
theorem carlsonPartialDeriv_regCarlsonSIntegral
    {b z : ι → ℂ} (hb : b ∈ mvBetaConvergent) (i : ι) :
    carlsonPartialDeriv i (regCarlsonSIntegral b) z =
      b i * regCarlsonSIntegral (addDirichletUnit b i) z := by
  rw [carlsonPartialDeriv, (hasDerivAt_regCarlsonSIntegral_update hb i).deriv]
  exact (mul_regDirichletIntegral_addDirichletUnit hb i
    (fun u ↦ exp (carlsonAffineForm z u))).symm

/-- Every iterated complex derivative of the exponential function is the exponential function
itself. -/
theorem iteratedDeriv_cexp_eq (n : ℕ) :
    iteratedDeriv n exp = exp := by
  simpa using iteratedDeriv_cexp_const_mul n 1

/-- Carlson's Theorem 5.8-2 in regularized integral form: replacing the averaged exponential
by any of its iterated derivatives does not change the `S` integral.  Carlson denotes the
left-hand side by `S⁽ⁿ⁾` and writes `S⁽ⁿ⁾ = S`. -/
theorem regCarlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      regCarlsonSIntegral b z := by
  rw [iteratedDeriv_cexp_eq]
  rfl

/-- Carlson's native, unregularized `S` integral.  Its intended integral interpretation
requires `b ∈ Complex.mvBetaConvergent`. -/
def carlsonSIntegral (b z : ι → ℂ) : ℂ :=
  Gamma (∑ i, b i) * regCarlsonSIntegral b z

/-- The unregularized and regularized native `S` integrals differ by `Γ(∑ i, b i)`. -/
theorem carlsonSIntegral_eq_Gamma_mul_reg (b z : ι → ℂ) :
    carlsonSIntegral b z = Gamma (∑ i, b i) * regCarlsonSIntegral b z := rfl

/-- Carlson's Theorem 5.8-2 for the unregularized native integral. -/
theorem carlsonDirichletAverage_iteratedDeriv_exp
    (n : ℕ) (b z : ι → ℂ) :
    Gamma (∑ i, b i) *
        regCarlsonDirichletAverage b z (iteratedDeriv n exp) =
      carlsonSIntegral b z := by
  rw [regCarlsonDirichletAverage_iteratedDeriv_exp]
  rfl

/-- A candidate is an entire regularized continuation of Carlson's `S` if it agrees with the
native regularized integral wherever all Dirichlet parameters have positive real part. -/
def IsRegCarlsonSContinuation (z : ι → ℂ) (G : (ι → ℂ) → ℂ) : Prop :=
  IsRegCarlsonContinuation exp z G

/-- A regularized Carlson `S` continuation is entire in the Dirichlet parameters. -/
theorem IsRegCarlsonSContinuation.analyticOnNhd {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) : AnalyticOnNhd ℂ G Set.univ :=
  hG.1

/-- A regularized Carlson `S` continuation agrees with the native integral on its ordinary
domain of absolute convergence. -/
theorem IsRegCarlsonSContinuation.eq_integral {z : ι → ℂ} {G : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    G b = regCarlsonSIntegral b z :=
  hG.2 hb

/-- An entire regularized continuation of Carlson's `S`, if it exists, is unique. -/
theorem IsRegCarlsonSContinuation.eq {z : ι → ℂ} {G H : (ι → ℂ) → ℂ}
    (hG : IsRegCarlsonSContinuation z G) (hH : IsRegCarlsonSContinuation z H) : G = H :=
  IsRegCarlsonContinuation.eq hG hH

/-- The series candidate for the entire regularized Carlson `S` function.  This is the
exponential specialization of Carlson's regularized Taylor construction. -/
def regCarlsonSSeries (z b : ι → ℂ) : ℂ :=
  regCarlsonTaylorSeries 0 (fun n ↦ (Nat.factorial n : ℂ)⁻¹) z b

/-- Carlson's formula (6.3-5), exposing the regularized `S` candidate as the exponential
generating series of the regularized `R` polynomials. -/
theorem regCarlsonSSeries_eq_tsum_regCarlsonR (z b : ι → ℂ) :
    regCarlsonSSeries z b =
      ∑' n : ℕ, (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b := by
  simp [regCarlsonSSeries, regCarlsonTaylorSeries]

/-- The `N`th partial sum in Carlson's exponential-series construction of the regularized
`S` function. -/
def regCarlsonSPartialSum (N : ℕ) (z b : ι → ℂ) : ℂ :=
  ∑ n ∈ Finset.range N, (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b

/-- Every partial sum in Carlson's construction is entire in the Dirichlet parameters. -/
theorem analyticOnNhd_regCarlsonSPartialSum (N : ℕ) (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonSPartialSum N z) Set.univ := by
  intro b _
  unfold regCarlsonSPartialSum
  apply Finset.analyticAt_fun_sum
  intro n _
  exact analyticAt_const.mul
    (analyticOnNhd_regCarlsonR n z b (Set.mem_univ b))

/-- Whenever Carlson's coefficient series is summable at `b`, its partial sums converge to
`regCarlsonSSeries z b`.  This separates the formal series construction from the estimates
needed to establish summability. -/
theorem tendsto_regCarlsonSPartialSum (z b : ι → ℂ)
    (h : Summable fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b) :
    Filter.Tendsto (fun N ↦ regCarlsonSPartialSum N z b) Filter.atTop
      (nhds (regCarlsonSSeries z b)) := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonR]
  exact h.hasSum.tendsto_sum_nat

/-- The exponential series of the Carlson affine form converges pointwise to the exponential
kernel. -/
theorem hasSum_exp_carlsonAffineForm (z : ι → ℂ) (u : ι → ℝ) :
    HasSum (fun n : ℕ ↦ carlsonAffineForm z u ^ n / Nat.factorial n)
      (exp (carlsonAffineForm z u)) :=
  by
    simpa [Complex.exp_eq_exp_ℂ] using
      (NormedSpace.expSeries_div_hasSum_exp (carlsonAffineForm z u))

/-- On the native convergence region, Carlson's exponential series is summable and its sum
is the regularized `S` integral.  This is the integral form of the power-series construction
in Sections 5.7--5.8. -/
theorem hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    HasSum (fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b)
      (regCarlsonSIntegral b z) := by
  let μ := (MeasureTheory.Measure.stdSimplexMeasure (ι := ι)).restrict (stdSimplex ℝ ι)
  let C : ℝ := ∑ i, ‖z i‖
  let M : ℕ → ℝ := fun n ↦ C ^ n / Nat.factorial n
  let F : ℕ → (ι → ℝ) → ℂ := fun n u ↦
    regDirichletDensity b u * (carlsonAffineForm z u ^ n / Nat.factorial n)
  let g : (ι → ℝ) → ℂ := fun u ↦
    regDirichletDensity b u * exp (carlsonAffineForm z u)
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ ↦ norm_nonneg _
  have hM : Summable M := by
    simpa [M] using Real.summable_pow_div_factorial C
  have hdens : Integrable (fun u ↦ regDirichletDensity b u) μ := by
    change IntegrableOn (fun u ↦ regDirichletDensity b u)
      (stdSimplex ℝ ι) MeasureTheory.Measure.stdSimplexMeasure
    simpa only [mul_one] using integrableOn_regDirichletDensity_mul b hb
      (continuousOn_const : ContinuousOn (fun _ : ι → ℝ ↦ (1 : ℂ))
        (stdSimplex ℝ ι))
  have hF_meas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    exact (integrableOn_regDirichletDensity_mul b hb
      ((continuous_carlsonAffineForm z).continuousOn.pow n |>.div_const _)).1
  have hbound (n : ℕ) : ∀ᵐ u ∂μ, ‖F n u‖ ≤ M n * ‖regDirichletDensity b u‖ := by
    filter_upwards [self_mem_ae_restrict
      (μ := MeasureTheory.Measure.stdSimplexMeasure)
      (isClosed_stdSimplex ℝ ι).measurableSet] with u hu
    simp only [F, M, norm_mul, norm_div, norm_natCast]
    calc
      ‖regDirichletDensity b u‖ * (‖carlsonAffineForm z u ^ n‖ / ↑n.factorial) ≤
          ‖regDirichletDensity b u‖ * (C ^ n / ↑n.factorial) := by
            apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
            apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
            rw [norm_pow]
            exact pow_le_pow_left₀ (norm_nonneg _)
              (norm_carlsonAffineForm_le_sum_norm z hu) n
      _ = C ^ n / ↑n.factorial * ‖regDirichletDensity b u‖ := by ring
  have hbound_summable : ∀ᵐ u ∂μ,
      Summable fun n ↦ M n * ‖regDirichletDensity b u‖ := by
    filter_upwards with u
    exact hM.mul_right _
  have hbound_integrable : Integrable
      (fun u ↦ ∑' n, M n * ‖regDirichletDensity b u‖) μ := by
    have heq : (fun u ↦ ∑' n, M n * ‖regDirichletDensity b u‖) =
        fun u ↦ (∑' n, M n) * ‖regDirichletDensity b u‖ := by
      funext u
      rw [tsum_mul_right]
    rw [heq]
    exact hdens.norm.const_mul _
  have hlim : ∀ᵐ u ∂μ, HasSum (fun n ↦ F n u) (g u) := by
    filter_upwards with u
    exact (hasSum_exp_carlsonAffineForm z u).mul_left (regDirichletDensity b u)
  have h := hasSum_integral_of_dominated_convergence
    (fun n u ↦ M n * ‖regDirichletDensity b u‖) hF_meas hbound
      hbound_summable hbound_integrable hlim
  have hterm (n : ℕ) : (∫ u, F n u ∂μ) =
      (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b := by
    rw [show (fun u ↦ F n u) = fun u ↦ (Nat.factorial n : ℂ)⁻¹ *
        (regDirichletDensity b u * carlsonAffineForm z u ^ n) by
      funext u
      simp [F, div_eq_mul_inv]
      ring]
    rw [integral_const_mul]
    rw [← regCarlsonDirichletAverage_pow n z hb]
    rfl
  simpa [g, μ, regCarlsonSIntegral, regCarlsonDirichletAverage,
    regDirichletIntegral] using h.congr_fun (fun n ↦ (hterm n).symm)

/-- Carlson's exponential series is summable throughout the native Dirichlet convergence
region. -/
theorem summable_regCarlsonR_div_factorial
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    Summable fun n : ℕ ↦ (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b :=
  (hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral z hb).summable

/-- On the native convergence region, the series construction of the regularized `S`
function agrees with its defining Dirichlet integral. -/
theorem regCarlsonSSeries_eq_regCarlsonSIntegral
    (z : ι → ℂ) {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonSSeries z b = regCarlsonSIntegral b z := by
  rw [regCarlsonSSeries_eq_tsum_regCarlsonR]
  exact (hasSum_regCarlsonR_div_factorial_eq_regCarlsonSIntegral z hb).tsum_eq

/-- Carlson's series construction is entire in all Dirichlet parameters.  This is the
analytic assertion in Corollary 6.3-3; its proof is the locally uniform version of the
coefficient estimate used above for pointwise summability. -/
theorem analyticOnNhd_regCarlsonSSeries (z : ι → ℂ) :
    AnalyticOnNhd ℂ (regCarlsonSSeries z) Set.univ := by
  rw [show regCarlsonSSeries z = fun b ↦ ∑' n : ℕ,
      (Nat.factorial n : ℂ)⁻¹ * regCarlsonR n z b by
    funext b
    exact regCarlsonSSeries_eq_tsum_regCarlsonR z b]
  apply analyticOnNhd_tsum_of_summable_norm_on_compacts isOpen_univ
  · intro n
    exact analyticOnNhd_const.mul (analyticOnNhd_regCarlsonR n z)
  · intro K hKuniv hK
    exact exists_summable_norm_regCarlsonR_div_factorial_on_compact_parameters z hK

/-- The exponential series realizes Carlson's entire regularized continuation of `S`. -/
theorem isRegCarlsonSContinuation_series (z : ι → ℂ) :
    IsRegCarlsonSContinuation z (regCarlsonSSeries z) := by
  refine ⟨analyticOnNhd_regCarlsonSSeries z, ?_⟩
  intro b hb
  exact regCarlsonSSeries_eq_regCarlsonSIntegral z hb

/-- The continued S-function is jointly entire in parameters and nodes, by locally uniform
convergence of the R-polynomial expansion.  A sum index encodes the two vectors. -/
theorem analyticOnNhd_regCarlsonSSeries_joint :
    AnalyticOnNhd ℂ (fun q : Sum ι ι → ℂ =>
      regCarlsonSSeries (fun i => q (.inr i)) (fun i => q (.inl i))) Set.univ := by
  simp_rw [regCarlsonSSeries_eq_tsum_regCarlsonR]
  apply analyticOnNhd_tsum_of_summable_norm_on_compacts isOpen_univ
  · intro n q _
    apply analyticAt_const.mul
    simp only [regCarlsonR, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
      carlsonRPolynomialNumerator_eq_multinomial_sum]
    apply AnalyticAt.mul
    · apply Finset.analyticAt_fun_sum
      intro m hm
      apply AnalyticAt.mul
      · apply AnalyticAt.mul analyticAt_const
        apply Finset.analyticAt_fun_prod
        intro i hi
        exact ((ContinuousLinearMap.proj (R := ℂ) (.inr i)).analyticAt q).pow _
      · apply Finset.analyticAt_fun_prod
        intro i hi
        exact ((AnalyticOnNhd.eval_polynomial (ascPochhammer ℂ (m i))) _
          (Set.mem_univ _)).comp ((ContinuousLinearMap.proj (R := ℂ) (.inl i)).analyticAt q)
    · have H := Complex.differentiable_one_div_Gamma.analyticAt
        (z := (∑ i, q (.inl i)) + n)
      have ht : AnalyticAt ℂ (fun q : Sum ι ι → ℂ => (∑ i, q (.inl i)) + n) q :=
        (Finset.analyticAt_fun_sum _ (fun i _ =>
          (ContinuousLinearMap.proj (R := ℂ) (.inl i)).analyticAt q)).add analyticAt_const
      simpa only [one_div] using! H.comp_of_eq ht rfl
  · intro K hKuniv hK
    have hc : Continuous (fun q : Sum ι ι → ℂ => ∑ i, ‖q (.inr i)‖) := by fun_prop
    obtain ⟨Z₀, hZ₀⟩ := hK.bddAbove_image hc.continuousOn
    have hp : Continuous (fun q : Sum ι ι → ℂ => fun i => q (.inl i)) := by fun_prop
    obtain ⟨M, hM, hbound⟩ :=
      exists_summable_norm_regCarlsonR_div_factorial_bounded_variables
        (hK.image hp) (le_max_right Z₀ 0)
    refine ⟨M, hM, fun n q hq => hbound n _ (Set.mem_image_of_mem _ hq) _ ?_⟩
    exact (hZ₀ (Set.mem_image_of_mem _ hq)).trans (le_max_left _ _)

/-- The continued S-function is entire in its node vector. -/
theorem analyticOnNhd_regCarlsonSSeries_variables (b : ι → ℂ) :
    AnalyticOnNhd ℂ (fun z : ι → ℂ => regCarlsonSSeries z b) Set.univ := by
  intro z _
  have hmap : AnalyticAt ℂ (fun z : ι → ℂ => Sum.elim b z) z := by
    apply AnalyticAt.pi
    intro k
    cases k with
    | inl i => exact analyticAt_const
    | inr i => exact (ContinuousLinearMap.proj (R := ℂ) i).analyticAt z
  have H := (analyticOnNhd_regCarlsonSSeries_joint (Sum.elim b z)
    (Set.mem_univ _)).comp_of_eq hmap rfl
  simpa only [Sum.elim_inl, Sum.elim_inr] using! H

/-- On the native Dirichlet convergence region, the regularized integral is jointly entire
in the Carlson variables. -/
theorem analyticOnNhd_regCarlsonSIntegral_variables {b : ι → ℂ}
    (hb : b ∈ mvBetaConvergent) :
    AnalyticOnNhd ℂ (regCarlsonSIntegral b) Set.univ := by
  change AnalyticOnNhd ℂ (fun z => regCarlsonDirichletAverage b z exp) Set.univ
  simpa using
    (analyticOnNhd_regCarlsonDirichletAverage_nodes
      (Ω := Set.univ) isOpen_univ (convex_univ : Convex ℝ (Set.univ : Set ℂ))
      analyticOnNhd_cexp hb)

/-- Carlson's differentiation formula for the analytically continued `S` function. -/
theorem carlsonPartialDeriv_regCarlsonSSeries (i : ι) (z b : ι → ℂ) :
    carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z =
      b i * regCarlsonSSeries z (addDirichletUnit b i) := by
  let F := fun q : Sum ι ι → ℂ =>
    regCarlsonSSeries (fun j => q (.inr j)) (fun j => q (.inl j))
  let d : Sum ι ι → ℂ := Pi.single (.inr i) 1
  have hF : AnalyticOnNhd ℂ F Set.univ := analyticOnNhd_regCarlsonSSeries_joint
  have hpartial (b : ι → ℂ) :
      carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z =
        fderiv ℂ F (Sum.elim b z) d := by
    have heq : (fun w => F (Function.update (Sum.elim b z) (.inr i) w)) =
        (fun w => regCarlsonSSeries (Function.update z i w) b) := by
      funext w
      dsimp only [F]
      congr 1
      · funext j; simp
    have hd : HasFDerivAt F (fderiv ℂ F (Sum.elim b z))
        (Function.update (Sum.elim b z) (.inr i) (z i)) := by
      simpa using (hF (Sum.elim b z) (Set.mem_univ _)).differentiableAt.hasFDerivAt
    have H := hd.comp_hasDerivAt (z i)
      (hasDerivAt_update (Sum.elim b z) (.inr i) (z i))
    rw [carlsonPartialDeriv, ← heq]
    exact H.deriv
  have hleft : AnalyticOnNhd ℂ
      (fun b => carlsonPartialDeriv i (fun z => regCarlsonSSeries z b) z) Set.univ := by
    simp_rw [hpartial]
    intro b _
    have hmap : AnalyticAt ℂ (fun b : ι → ℂ => Sum.elim b z) b := by
      apply AnalyticAt.pi
      intro k
      cases k with
      | inl j => exact (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
      | inr j => exact analyticAt_const
    exact ((ContinuousLinearMap.apply ℂ ℂ d).analyticAt _).comp
      (((hF _ (Set.mem_univ _)).fderiv).comp hmap)
  have hright : AnalyticOnNhd ℂ
      (fun b => b i * regCarlsonSSeries z (addDirichletUnit b i)) Set.univ := by
    intro b _
    apply ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).mul
    apply (analyticOnNhd_regCarlsonSSeries z _ (Set.mem_univ _)).comp
    apply AnalyticAt.pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [addDirichletUnit] using!
        ((ContinuousLinearMap.proj (R := ℂ) i).analyticAt b).add analyticAt_const
    · simpa [addDirichletUnit, hji] using!
        (ContinuousLinearMap.proj (R := ℂ) j).analyticAt b
  have heq := analyticOnNhd_eq_of_eqOn_mvBetaConvergent hleft hright (by
    intro b hb
    have hf : (fun z => regCarlsonSSeries z b) = regCarlsonSIntegral b :=
      funext fun z => regCarlsonSSeries_eq_regCarlsonSIntegral z hb
    dsimp only
    rw [hf, carlsonPartialDeriv_regCarlsonSIntegral hb,
      regCarlsonSSeries_eq_regCarlsonSIntegral z (addDirichletUnit_mem_mvBetaConvergent hb i)])
  exact congrFun heq b

/-- Simultaneous permutation of the Dirichlet parameters and variables leaves the native
regularized `S` integral unchanged. -/
theorem regCarlsonSIntegral_perm (b z : ι → ℂ) (σ : Equiv.Perm ι) :
    regCarlsonSIntegral (b ∘ σ) (z ∘ σ) = regCarlsonSIntegral b z :=
  regCarlsonDirichletAverage_perm b z exp σ

/-- Translating every variable by `a` multiplies the native regularized `S` integral by
`exp a`.  This is Carlson's exponential translation identity. -/
theorem regCarlsonSIntegral_add_const (b z : ι → ℂ) (a : ℂ) :
    regCarlsonSIntegral b (fun i ↦ z i + a) = exp a * regCarlsonSIntegral b z := by
  unfold regCarlsonSIntegral
  rw [show (fun i ↦ z i + a) = (fun i ↦ 1 * z i + a) by funext i; simp]
  rw [← regCarlsonDirichletAverage_comp_affine b z exp 1 a]
  unfold regCarlsonDirichletAverage regDirichletIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rw [one_mul, exp_add]
  ring

/-- Translation of all variables for Carlson's analytically continued `S` function.  This
global identity follows from the native integral identity and uniqueness of continuation in
the Dirichlet parameters. -/
theorem regCarlsonSSeries_add_const (z b : ι → ℂ) (a : ℂ) :
    regCarlsonSSeries (fun i => z i + a) b = exp a * regCarlsonSSeries z b := by
  let z' : ι → ℂ := fun i => z i + a
  have hleft : IsRegCarlsonSContinuation z' (regCarlsonSSeries z') :=
    isRegCarlsonSContinuation_series z'
  have hright : IsRegCarlsonSContinuation z'
      (fun b => exp a * regCarlsonSSeries z b) := by
    refine ⟨?_, ?_⟩
    · intro b hb
      exact analyticAt_const.mul
        (analyticOnNhd_regCarlsonSSeries z b (Set.mem_univ b))
    · intro b hb
      dsimp only
      rw [regCarlsonSSeries_eq_regCarlsonSIntegral z hb]
      exact (regCarlsonSIntegral_add_const b z a).symm
  exact congrFun (hleft.eq hright) b

/-- At the zero variable vector, the native regularized `S` integral is the reciprocal Gamma
factor on the ordinary convergence domain. -/
theorem regCarlsonSIntegral_zero {b : ι → ℂ} (hb : b ∈ mvBetaConvergent) :
    regCarlsonSIntegral b (fun _ ↦ 0) = 1 / Gamma (∑ i, b i) := by
  simpa [regCarlsonSIntegral] using
    (regCarlsonDirichletAverage_const exp 0 hb)

/- The three analytic obligations above deliberately expose the remaining locally uniform
series argument.  All pointwise summability and integral agreement needed by that argument
have already been proved in this file. -/

end DirichletTransform

end CarlsonS
