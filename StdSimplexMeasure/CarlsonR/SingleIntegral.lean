/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
module

public import StdSimplexMeasure.CarlsonR.SlitPlane
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

import Pochhammer.Gamma
import Pochhammer.BinomialSeries
import SeveralComplexVariables.ParametricIntegral
import StdSimplexMeasure.CarlsonDirichletAverage.PowerSeries
import StdSimplexMeasure.CarlsonR.Deriv
import StdSimplexMeasure.CarlsonRPolynomial.Generating

/-!
# Single-integral representations of Carlson's R-function

This file is the home for Carlson's Theorem 6.8-1.  The unit-interval and positive-ray
forms below are branch-safe because every Carlson variable is required to lie in the open
right half-plane.
-/

open Complex MeasureTheory ProbabilityTheory
open scoped Classical

@[expose] public noncomputable section CarlsonR

namespace DirichletTransform

variable {ι : Type*} [Fintype ι]

/-- The beta-weighted unit-interval integral in Carlson's single-integral representation. -/
def carlsonRUnitIntervalIntegral (a a' : ℂ) (b z : ι → ℂ) : ℂ :=
  ∫ u : ℝ in Set.Ioo 0 1,
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
      ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)

/-- Shifting the first parameter of the beta integral by a natural number introduces
the corresponding Pochhammer factor. -/
private lemma betaIntegral_add_nat_left (a a' : ℂ) (n : ℕ)
    (ha : 0 < a.re) (ha' : 0 < a'.re) :
    betaIntegral (a + n) a' =
      betaIntegral a a' * Gamma (a + a') *
        (ascPochhammer ℂ n).eval a * (Gamma (a + a' + n))⁻¹ := by
  have han : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
  have hc : 0 < (a + a').re := by simpa only [add_re] using add_pos ha ha'
  have hcn : 0 < (a + a' + n).re := by simp only [add_re, natCast_re]; positivity
  have hGa : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have hGc : Gamma (a + a') ≠ 0 := Gamma_ne_zero_of_re_pos hc
  have hGan : Gamma (a + n) ≠ 0 := Gamma_ne_zero_of_re_pos han
  have hGcn : Gamma (a + a' + n) ≠ 0 := Gamma_ne_zero_of_re_pos hcn
  have hpa : Gamma (a + n) = (ascPochhammer ℂ n).eval a * Gamma a := by
    have h := Gamma_add_nat_div_Gamma_eq (n := n) a (fun k hEq => by
      have := congrArg Complex.re hEq
      simp only [neg_re, natCast_re] at this
      linarith)
    exact (div_eq_iff hGa).mp h
  have hadd : a + n + a' = a + a' + n := by ring
  rw [betaIntegral_eq_Gamma_mul_div _ _ han ha',
    betaIntegral_eq_Gamma_mul_div _ _ ha ha', hpa, hadd]
  field_simp

/-- The generating series of the product kernel appearing in the unit-interval integral. -/
private lemma hasSum_singleIntegral_kernel
    (b y : ι → ℂ) {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1)
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonRPolynomialNumerator n b y / (n.factorial : ℂ) * (u : ℂ) ^ n)
      (∏ i, (1 - (u : ℂ) * y i) ^ (-b i)) := by
  have hgen := hasSum_carlsonRPolynomialNumerator_div_factorial b y (u : ℂ)
    (fun i => by
      rw [norm_mul]
      simp only [norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) hu1) (hy i))
  convert hgen using 1
  unfold carlsonRGeneratingKernel
  apply Finset.prod_congr rfl
  intro i hi
  rw [Complex.cpow_neg]
  exact (one_div _).symm

/-- Near the all-one Carlson variable, the unit-interval integral is the termwise beta
integral of the generating series for the R-polynomials. -/
private lemma hasSum_carlsonRUnitIntervalIntegral
    (a a' : ℂ) (b y : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonRPolynomialNumerator n b y / (n.factorial : ℂ) *
        betaIntegral (a + n) a')
      (carlsonRUnitIntervalIntegral a a' b (fun i => 1 - y i)) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  let K : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)
  let A : ℕ → ℂ := fun n =>
    carlsonRPolynomialNumerator n b y / (n.factorial : ℂ)
  let F : ℕ → ℝ → ℂ := fun n u => K u * (A n * (u : ℂ) ^ n)
  let f : ℝ → ℂ := fun u => K u * ∏ i, (1 - (u : ℂ) * y i) ^ (-b i)
  let M : ℕ → ℝ := fun n => ‖A n‖
  let B : ℕ → ℝ → ℝ := fun n u => M n * ‖K u‖
  have hAsum : Summable A := by
    simpa [A] using summable_carlsonRPolynomialNumerator_div_factorial b y 1
      (by simpa using hy)
  have hM : Summable M := by simpa [M] using hAsum.norm
  have hKint : Integrable K μ := by
    change IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)) (Set.Ioo 0 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent ha ha')
  have hterm_point (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
      F n u = A n *
        ((u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1)) := by
    have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
    simp only [F, K]
    calc
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * (A n * (u : ℂ) ^ n) =
          A n * (((u : ℂ) ^ (a - 1) * (u : ℂ) ^ n) *
            (1 - u : ℂ) ^ (a' - 1)) := by ring
      _ = A n * ((u : ℂ) ^ ((a - 1) + n) * (1 - u : ℂ) ^ (a' - 1)) := by
        rw [← Complex.cpow_natCast, Complex.cpow_add _ _ hu0]
      _ = A n * ((u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1)) := by
        congr 3
        ring
  have hFint (n : ℕ) : Integrable (F n) μ := by
    have han : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
    have hbase : IntegrableOn (fun u : ℝ =>
        (u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1))
        (Set.Ioo 0 1) volume :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
        (betaIntegral_convergent han ha')
    exact (hbase.const_mul (A n)).congr <| by
      filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      exact (hterm_point n hu).symm
  have hBsum : ∀ᵐ u ∂μ, Summable fun n => B n u := by
    filter_upwards with u
    exact hM.mul_right _
  have hBint : Integrable (fun u => ∑' n, B n u) μ := by
    have heq : (fun u => ∑' n, B n u) = fun u => (∑' n, M n) * ‖K u‖ := by
      funext u
      simp only [B]
      rw [tsum_mul_right]
    rw [heq]
    exact hKint.norm.const_mul _
  have hbound (n : ℕ) : ∀ᵐ u ∂μ, ‖F n u‖ ≤ B n u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    simp only [F, B, M, norm_mul]
    have hu_norm : ‖(u : ℂ)‖ ≤ 1 := by
      simp only [norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact hu.2.le
    rw [norm_pow]
    calc
      ‖K u‖ * (‖A n‖ * ‖(u : ℂ)‖ ^ n) ≤ ‖K u‖ * (‖A n‖ * 1 ^ n) := by
        gcongr
      _ = ‖A n‖ * ‖K u‖ := by ring
  have hlim : ∀ᵐ u ∂μ, HasSum (fun n => F n u) (f u) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (hasSum_singleIntegral_kernel b y hu.1.le hu.2.le hy).mul_left (K u)
  have hseries := hasSum_integral_of_dominated_convergence B
    (fun n => (hFint n).aestronglyMeasurable) hbound hBsum hBint hlim
  have hterm (n : ℕ) : ∫ u, F n u ∂μ = A n * betaIntegral (a + n) a' := by
    rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one,
      ← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact hterm_point n hu
  have hfun : (fun n => ∫ u, F n u ∂μ) =
      fun n => A n * betaIntegral (a + n) a' := funext hterm
  rw [hfun] at hseries
  convert hseries using 1
  · rfl
  · unfold carlsonRUnitIntervalIntegral f K μ
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    congr 1
    ring

/-- A convex combination of the entries of a vector is bounded by its supremum norm. -/
private lemma norm_carlsonAffineForm_le_pi_norm
    (y : ι → ℂ) {u : ι → ℝ} (hu : u ∈ stdSimplex ℝ ι) :
    ‖carlsonAffineForm y u‖ ≤ ‖y‖ := by
  unfold carlsonAffineForm
  calc
    ‖∑ i, (u i : ℂ) * y i‖ ≤ ∑ i, ‖(u i : ℂ) * y i‖ := norm_sum_le _ _
    _ = ∑ i, u i * ‖y i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    _ ≤ ∑ i, u i * ‖y‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm y i) (hu.1 i)
    _ = ‖y‖ := by rw [← Finset.sum_mul, hu.2, one_mul]

set_option maxHeartbeats 2000000 in
/-- The regularized R-integral has its R-polynomial expansion near the all-one variable. -/
private lemma hasSum_regCarlsonRIntegral_near_one
    (a : ℂ) (b y : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (fun n : ℕ =>
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * regCarlsonR n y b)
      (regCarlsonRIntegral (-a) b (fun i => 1 - y i)) := by
  let coeff : ℕ → ℂ := fun n =>
    (-1 : ℂ) ^ n * ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ))
  let M : ℕ → ℝ := fun n =>
    ‖(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * ((‖y‖ : ℂ) ^ n)‖
  have hynorm : ‖y‖ < 1 := (pi_norm_lt_iff zero_lt_one).2 hy
  have hM : Summable M := by
    simpa [M] using summable_norm_ascPochhammer_mul_pow_div_factorial a (‖y‖ : ℂ)
      (by simpa using hynorm)
  have hbound : ∀ n u, u ∈ stdSimplex ℝ ι →
      ‖coeff n * (carlsonAffineForm (fun i => 1 - y i) u - 1) ^ n‖ ≤ M n := by
    intro n u hu
    have haff : carlsonAffineForm (fun i => 1 - y i) u - 1 =
        -carlsonAffineForm y u := by
      rw [show (fun i => 1 - y i) = fun i => (-1 : ℂ) * y i + 1 by
        funext i; ring]
      rw [carlsonAffineForm_affine hu]
      ring
    simp only [coeff, M, haff, norm_mul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
    simp only [norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg y)]
    gcongr
    exact norm_carlsonAffineForm_le_pi_norm y hu
  have hpoint : ∀ u, u ∈ stdSimplex ℝ ι →
      HasSum (fun n => coeff n *
        (carlsonAffineForm (fun i => 1 - y i) u - 1) ^ n)
        (carlsonAffineForm (fun i => 1 - y i) u ^ (-a)) := by
    intro u hu
    have haff : carlsonAffineForm (fun i => 1 - y i) u =
        1 - carlsonAffineForm y u := by
      rw [show (fun i => 1 - y i) = fun i => (-1 : ℂ) * y i + 1 by
        funext i; ring]
      rw [carlsonAffineForm_affine hu]
      ring
    have hq : ‖carlsonAffineForm y u‖ < 1 :=
      lt_of_le_of_lt (norm_carlsonAffineForm_le_pi_norm y hu) hynorm
    have hs := hasSum_ascPochhammer_mul_pow_div_factorial a
      (carlsonAffineForm y u) hq
    convert hs using 1
    · funext n
      simp only [coeff, haff]
      rw [show 1 - carlsonAffineForm y u - 1 = -carlsonAffineForm y u by ring,
        neg_pow]
      ring_nf
      rw [show n * 2 = 2 * n by omega, pow_mul]
      simp
    · rw [haff, Complex.cpow_neg]
      exact (one_div _).symm
  have hs := hasSum_regCarlsonR_of_powerSeries hb 1 coeff
    (fun i => 1 - y i) (fun w => w ^ (-a)) M hM hbound hpoint
  have hshift : shiftCarlsonVariables 1 (fun i => 1 - y i) =
      fun i => (-1 : ℂ) * y i := by
    funext i
    simp [shiftCarlsonVariables]
  have hterms : (fun n => coeff n *
      regCarlsonR n (shiftCarlsonVariables 1 (fun i => 1 - y i)) b) =
      fun n => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
        regCarlsonR n y b := by
    funext n
    rw [hshift, regCarlsonR_smul_of_mem_mvBetaConvergent n (-1) y hb]
    simp only [coeff]
    ring_nf
    rw [show n * 2 = 2 * n by omega, pow_mul]
    simp
  rw [hterms] at hs
  simpa [regCarlsonRIntegral] using hs

/-- Carlson's single-integral identity in the polydisc centered at the all-one variable. -/
private lemma carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : ∀ i, ‖1 - z i‖ < 1) :
    carlsonRUnitIntervalIntegral a a' b z =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  let y : ι → ℂ := fun i => 1 - z i
  have hy : ∀ i, ‖y i‖ < 1 := hz
  have hzback : (fun i => 1 - y i) = z := by
    funext i
    simp [y]
  have hunit := hasSum_carlsonRUnitIntervalIntegral a a' b y ha ha' hy
  rw [hzback] at hunit
  have hr := (hasSum_regCarlsonRIntegral_near_one a b y hb hy).mul_left
    (betaIntegral a a' * Gamma (∑ i, b i))
  rw [hzback] at hr
  have hterms : (fun n : ℕ =>
      carlsonRPolynomialNumerator n b y / (n.factorial : ℂ) *
        betaIntegral (a + n) a') =
      fun n => (betaIntegral a a' * Gamma (∑ i, b i)) *
        ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * regCarlsonR n y b) := by
    funext n
    change carlsonRPolynomialNumerator n b y / (n.factorial : ℂ) *
        betaIntegral (a + n) a' =
      (betaIntegral a a' * Gamma (∑ i, b i)) *
        ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
          regCarlsonRPolynomial n b y)
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
    rw [← hsum]
    rw [betaIntegral_add_nat_left a a' n ha ha']
    ring
  rw [hterms] at hunit
  exact hunit.unique (by
    simpa [carlsonRIntegral, mul_assoc] using hr)

omit [Fintype ι] in
/-- The affine segment from `1` to a point in Carlson's right-half-plane domain remains in
that domain. -/
private lemma affineSegment_mem_rightHalfPlane
    {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) (i : ι) :
    (1 - u : ℂ) + (u : ℂ) * z i ∈ carlsonRightHalfPlane := by
  have hzi : 0 < (z i).re := hz i
  by_cases hu0 : u = 0
  · subst u
    simp [carlsonRightHalfPlane]
  have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
  have hmul : 0 < u * (z i).re := mul_pos hupos hzi
  have hone : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq]
  simp only [add_re, sub_re, one_re, ofReal_re, mul_re, ofReal_im, zero_mul, sub_zero]
  exact add_pos_of_nonneg_of_pos hone hmul

/-- The product kernel in Carlson's single-integral formula. -/
private def singleIntegralKernel (b z : ι → ℂ) (u : ℝ) : ℂ :=
  ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)

/-- The Fréchet derivative of the product kernel with respect to the Carlson variables. -/
private def singleIntegralKernelFDeriv (b z : ι → ℂ) (u : ℝ) :
    (ι → ℂ) →L[ℂ] ℂ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i,
      ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) •
    ((-b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) •
      ((u : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)))

/-- The displayed derivative is the derivative of the single-integral product kernel. -/
private lemma hasFDerivAt_singleIntegralKernel
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain)
    {u : ℝ} (hu : u ∈ Set.Icc 0 1) :
    HasFDerivAt (fun y => singleIntegralKernel b y u)
      (singleIntegralKernelFDeriv b z u) z := by
  classical
  let p : ι → ((ι → ℂ) →L[ℂ] ℂ) := fun i => ContinuousLinearMap.proj i
  have hq (i : ι) : HasFDerivAt
      (fun y : ι → ℂ => (1 - u : ℂ) + (u : ℂ) * y i) ((u : ℂ) • p i) z := by
    simpa [p] using (((p i).hasFDerivAt.const_mul (u : ℂ)).const_add (1 - u : ℂ))
  have hpow (i : ι) : HasFDerivAt
      (fun y : ι → ℂ => ((1 - u : ℂ) + (u : ℂ) * y i) ^ (-b i))
      ((-b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) •
        ((u : ℂ) • p i)) z := by
    have h := (hq i).cpow (hasFDerivAt_const (x := z) (-b i))
      (carlsonRightHalfPlane_subset_slitPlane (affineSegment_mem_rightHalfPlane hz hu i))
    refine h.congr_fderiv ?_
    apply ContinuousLinearMap.ext
    intro v
    simp [p, neg_mul, smul_smul]
  exact HasFDerivAt.finsetProd (u := (Finset.univ : Finset ι))
    (fun i hi => hpow i)

/-- The kernel derivative is continuous jointly in its variables away from the branch cut. -/
private lemma continuousOn_singleIntegralKernelFDeriv
    (b : ι → ℂ) {S : Set ((ι → ℂ) × ℝ)}
    (hS : ∀ p ∈ S, ∀ i,
      (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i ∈ slitPlane) :
    ContinuousOn (fun p => singleIntegralKernelFDeriv b p.1 p.2) S := by
  classical
  have hq (i : ι) : Continuous
      (fun p : (ι → ℂ) × ℝ => (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) := by
    fun_prop
  have hpow (e : ι → ℂ) (i : ι) : ContinuousOn
      (fun p : (ι → ℂ) × ℝ =>
        ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) ^ e i) S :=
    (hq i).continuousOn.cpow continuousOn_const (fun p hp => hS p hp i)
  unfold singleIntegralKernelFDeriv
  apply continuousOn_finsetSum
  intro i hi
  have hout : ContinuousOn (fun p : (ι → ℂ) × ℝ =>
      ∏ j ∈ Finset.univ.erase i,
        ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 j) ^ (-b j)) S := by
    apply continuousOn_finsetProd
    intro j hj
    exact hpow (fun j => -b j) j
  have hscalar : ContinuousOn (fun p : (ι → ℂ) × ℝ =>
      -b i * ((1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i) ^ (-b i - 1)) S :=
    continuousOn_const.mul (hpow (fun j => -b j - 1) i)
  have hproj : Continuous (fun p : (ι → ℂ) × ℝ =>
      (p.2 : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)) := by
    fun_prop
  exact hout.smul (hscalar.smul hproj.continuousOn)

/-- At fixed Carlson variables in the right half-plane, the product kernel is continuous on
the closed unit interval. -/
private lemma continuousOn_singleIntegralKernel_fixed
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    ContinuousOn (singleIntegralKernel b z) (Set.Icc 0 1) := by
  classical
  unfold singleIntegralKernel
  apply continuousOn_finsetProd
  intro i hi
  have hq : Continuous
      (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z i) := by fun_prop
  exact hq.continuousOn.cpow continuousOn_const (fun u hu =>
    carlsonRightHalfPlane_subset_slitPlane (affineSegment_mem_rightHalfPlane hz hu i))

/-- At fixed Carlson variables in the right half-plane, the kernel derivative is continuous
on the closed unit interval. -/
private lemma continuousOn_singleIntegralKernelFDeriv_fixed
    (b : ι → ℂ) {z : ι → ℂ} (hz : z ∈ carlsonRVariableDomain) :
    ContinuousOn (singleIntegralKernelFDeriv b z) (Set.Icc 0 1) := by
  classical
  have hq (i : ι) : Continuous
      (fun u : ℝ => (1 - u : ℂ) + (u : ℂ) * z i) := by fun_prop
  have hpow (e : ι → ℂ) (i : ι) : ContinuousOn
      (fun u : ℝ => ((1 - u : ℂ) + (u : ℂ) * z i) ^ e i) (Set.Icc 0 1) :=
    (hq i).continuousOn.cpow continuousOn_const (fun u hu =>
      carlsonRightHalfPlane_subset_slitPlane (affineSegment_mem_rightHalfPlane hz hu i))
  unfold singleIntegralKernelFDeriv
  apply continuousOn_finsetSum
  intro i hi
  have hout : ContinuousOn (fun u : ℝ =>
      ∏ j ∈ Finset.univ.erase i,
        ((1 - u : ℂ) + (u : ℂ) * z j) ^ (-b j)) (Set.Icc 0 1) := by
    apply continuousOn_finsetProd
    intro j hj
    exact hpow (fun j => -b j) j
  have hscalar : ContinuousOn (fun u : ℝ =>
      -b i * ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i - 1)) (Set.Icc 0 1) :=
    continuousOn_const.mul (hpow (fun j => -b j - 1) i)
  have hproj : Continuous (fun u : ℝ =>
      (u : ℂ) • (ContinuousLinearMap.proj i : (ι → ℂ) →L[ℂ] ℂ)) := by fun_prop
  exact hout.smul (hscalar.smul hproj.continuousOn)

set_option maxHeartbeats 2000000 in
/-- For positive beta exponents, the unit-interval integral is analytic in all Carlson
variables throughout the right-half-plane domain. -/
theorem analyticOnNhd_carlsonRUnitIntervalIntegral
    (a a' : ℂ) (b : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re) :
    AnalyticOnNhd ℂ (carlsonRUnitIntervalIntegral a a' b)
      carlsonRVariableDomain := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo 0 1)
  let W : ℝ → ℂ := fun u =>
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)
  let F : (ι → ℂ) → ℝ → ℂ := fun z u => W u * singleIntegralKernel b z u
  let F' : (ι → ℂ) → ℝ → ((ι → ℂ) →L[ℂ] ℂ) := fun z u =>
    W u • singleIntegralKernelFDeriv b z u
  have hWint : Integrable W μ := by
    change IntegrableOn (fun u : ℝ =>
      (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)) (Set.Ioo 0 1) volume
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp
      (betaIntegral_convergent ha ha')
  have hU := isOpen_carlsonRVariableDomain (ι := ι)
  have hanalytic : AnalyticOnNhd ℂ (fun z => ∫ u, F z u ∂μ)
      carlsonRVariableDomain := by
    refine analyticOnNhd_integral_of_dominated_of_fderiv_le hU ?_
    intro z hz
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hU z hz
    let r : ℝ := ε / 2
    have hr : 0 < r := half_pos hε
    let Kset : Set ((ι → ℂ) × ℝ) := Metric.closedBall z r ×ˢ Set.Icc 0 1
    have hclosed_mem : Metric.closedBall z r ∈ nhds z := Metric.closedBall_mem_nhds z hr
    have hclosed_domain : Metric.closedBall z r ⊆ carlsonRVariableDomain := by
      intro y hy
      apply hball
      rw [Metric.mem_closedBall] at hy
      exact Metric.mem_ball.mpr (hy.trans_lt (half_lt_self hε))
    have hslit : ∀ p ∈ Kset, ∀ i,
        (1 - p.2 : ℂ) + (p.2 : ℂ) * p.1 i ∈ slitPlane := by
      intro p hp i
      exact carlsonRightHalfPlane_subset_slitPlane
        (affineSegment_mem_rightHalfPlane (hclosed_domain hp.1) hp.2 i)
    have hDcont : ContinuousOn
        (fun p => singleIntegralKernelFDeriv b p.1 p.2) Kset :=
      continuousOn_singleIntegralKernelFDeriv b hslit
    have hKcompact : IsCompact Kset := (isCompact_closedBall z r).prod isCompact_Icc
    obtain ⟨C₀, hC₀⟩ := bddAbove_def.mp (hKcompact.bddAbove_image hDcont.norm)
    let C : ℝ := max C₀ 0
    have hC : ∀ p ∈ Kset, ‖singleIntegralKernelFDeriv b p.1 p.2‖ ≤ C := by
      intro p hp
      exact (hC₀ _ ⟨p, hp, rfl⟩).trans (le_max_left _ _)
    let bound : ℝ → ℝ := fun u => C * ‖W u‖
    have hFint (y : ι → ℂ) (hy : y ∈ Metric.closedBall z r) : Integrable (F y) μ := by
      have hinterval := (betaIntegral_convergent ha ha').mul_continuousOn
        (by simpa [Set.uIcc_of_le zero_le_one] using
          continuousOn_singleIntegralKernel_fixed b (hclosed_domain hy))
      change IntegrableOn (fun u => W u * singleIntegralKernel b y u)
        (Set.Ioo 0 1) volume
      exact (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hinterval
    refine ⟨Metric.closedBall z r, bound, F', hclosed_mem, ?_, hFint z
      (Metric.mem_closedBall_self hr.le), ?_, ?_, ?_, ?_⟩
    · filter_upwards [hclosed_mem] with y hy
      exact (hFint y hy).aestronglyMeasurable
    · have hinterval := (betaIntegral_convergent ha ha').smul_continuousOn
          (by simpa [Set.uIcc_of_le zero_le_one] using
            continuousOn_singleIntegralKernelFDeriv_fixed b hz)
      exact ((intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp hinterval).1
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      intro y hy
      simp only [F', bound, norm_smul]
      calc
        ‖W u‖ * ‖singleIntegralKernelFDeriv b y u‖ ≤ ‖W u‖ * C := by
          gcongr
          exact hC (y, u) ⟨hy, hu.1.le, hu.2.le⟩
        _ = C * ‖W u‖ := mul_comm _ _
    · exact hWint.norm.const_mul C
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
      intro y hy
      have hyDomain := hclosed_domain hy
      have hder := (hasFDerivAt_singleIntegralKernel b hyDomain
        ⟨hu.1.le, hu.2.le⟩).const_mul (W u)
      simpa [F, F'] using hder
  change AnalyticOnNhd ℂ (fun z => ∫ u, F z u ∂μ) carlsonRVariableDomain
  exact hanalytic

/-- Carlson's Theorem 6.8-1 in unit-interval form.  The homogeneity relation
`a + a' = ∑ i, b i` supplies the exponent at the endpoint `u = 1`. -/
theorem carlsonRUnitIntervalIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRUnitIntervalIntegral a a' b z =
      betaIntegral a a' * carlsonRIntegral (-a) b z := by
  let one : ι → ℂ := fun _ => 1
  have hone : one ∈ carlsonRVariableDomain := by
    intro i
    simp [one, carlsonRightHalfPlane]
  have hconv : Convex ℝ (carlsonRVariableDomain : Set (ι → ℂ)) := by
    rw [show carlsonRVariableDomain (ι := ι) =
        Set.pi Set.univ (fun _ => carlsonRightHalfPlane) by
      ext w
      simp [carlsonRVariableDomain]]
    exact convex_pi (fun _ _ => convex_carlsonRightHalfPlane)
  have hleft := analyticOnNhd_carlsonRUnitIntervalIntegral a a' b ha ha'
  have hright : AnalyticOnNhd ℂ
      (fun w => betaIntegral a a' * carlsonRIntegral (-a) b w)
      carlsonRVariableDomain :=
    analyticOnNhd_const.mul (analyticOnNhd_carlsonRIntegral (-a) hb)
  have hevent : (carlsonRUnitIntervalIntegral a a' b) =ᶠ[nhds one]
      (fun w => betaIntegral a a' * carlsonRIntegral (-a) b w) := by
    filter_upwards [Metric.ball_mem_nhds one zero_lt_one] with w hw
    apply carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one ha ha' hsum hb
    intro i
    calc
      ‖1 - w i‖ = ‖(w - one) i‖ := by
        change ‖(1 : ℂ) - w i‖ = ‖w i - 1‖
        exact norm_sub_rev _ _
      _ ≤ ‖w - one‖ := norm_le_pi_norm (w - one) i
      _ = dist w one := by rw [dist_eq_norm]
      _ < 1 := Metric.mem_ball.mp hw
  exact hleft.eqOn_of_preconnected_of_eventuallyEq hright hconv.isPreconnected hone hevent hz

/-- The positive-ray form of Carlson's single-integral representation. -/
def carlsonRPositiveRayIntegral (a : ℂ) (b z : ι → ℂ) : ℂ :=
  ∫ s : ℝ in Set.Ioi 0,
    (s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i)

/-- The reciprocal translation `s ↦ (s + 1)⁻¹` maps the positive ray onto the open unit
interval. -/
private lemma image_recip_add_one_Ioi :
    (fun s : ℝ => (s + 1)⁻¹) '' Set.Ioi 0 = Set.Ioo 0 1 := by
  ext u
  constructor
  · rintro ⟨s, hs, rfl⟩
    change 0 < s at hs
    constructor
    · exact inv_pos.mpr (by linarith)
    · rw [inv_lt_one₀ (by linarith : 0 < s + 1)]
      linarith
  · intro hu
    refine ⟨u⁻¹ - 1, ?_, ?_⟩
    · change 0 < u⁻¹ - 1
      rw [sub_pos]
      exact (one_lt_inv₀ hu.1).2 hu.2
    · have hu0 : u ≠ 0 := hu.1.ne'
      field_simp
      ring

/-- The reciprocal translation is injective on the positive ray. -/
private lemma injOn_recip_add_one :
    Set.InjOn (fun s : ℝ => (s + 1)⁻¹) (Set.Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  have hx0 : x + 1 ≠ 0 := by linarith
  have hy0 : y + 1 ≠ 0 := by linarith
  exact add_right_cancel (inv_injective hxy)

/-- Derivative of the reciprocal translation on the positive ray. -/
private lemma hasDerivAt_recip_add_one (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun x : ℝ => (x + 1)⁻¹) (-((s + 1) ^ 2)⁻¹) s := by
  have hs0 : s + 1 ≠ 0 := by linarith
  convert! ((hasDerivAt_id s).add_const 1 |>.inv hs0) using 1
  all_goals simp only [id_eq]
  all_goals ring

/-- Complex powers split over a product whose first factor is a positive real number. -/
private lemma ofReal_mul_cpow {r : ℝ} (hr : 0 < r) {x e : ℂ} (hx : x ≠ 0) :
    ((r : ℂ) * x) ^ e = (r : ℂ) ^ e * x ^ e := by
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero hr0 hx),
    Complex.cpow_def_of_ne_zero hr0, Complex.cpow_def_of_ne_zero hx,
    Complex.log_ofReal_mul hr hx, ofReal_log hr.le, add_mul, Complex.exp_add]

omit [Fintype ι] in
/-- A finite product of complex powers with the same nonzero base combines by adding the
exponents. -/
private lemma prod_cpow_same_base
    (s : Finset ι) (r : ℂ) (hr : r ≠ 0) (e : ι → ℂ) :
    ∏ i ∈ s, r ^ e i = r ^ (∑ i ∈ s, e i) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, ← Complex.cpow_add _ _ hr]

set_option maxHeartbeats 800000 in
/-- Pointwise form of the reciprocal-translation substitution relating Carlson's ray and
unit-interval integrands. -/
private lemma ray_substitution_point
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain)
    {s : ℝ} (hs : s ∈ Set.Ioi 0) :
    |-((s + 1) ^ 2)⁻¹| •
        (((((s + 1)⁻¹ : ℝ) : ℂ) ^ (a' - 1) *
          (1 - (((s + 1)⁻¹ : ℝ) : ℂ)) ^ (a - 1)) *
          ∏ i, ((1 - (((s + 1)⁻¹ : ℝ) : ℂ)) +
            (((s + 1)⁻¹ : ℝ) : ℂ) * z i) ^ (-b i)) =
      (s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
  change 0 < s at hs
  let d : ℝ := s + 1
  let r : ℝ := d⁻¹
  have hd : 0 < d := by dsimp [d]; linarith
  have hr : 0 < r := inv_pos.mpr hd
  have hr0 : (r : ℂ) ≠ 0 := ofReal_ne_zero.mpr hr.ne'
  have habs : |-((s + 1) ^ 2)⁻¹| = r ^ 2 := by
    dsimp [r, d]
    rw [abs_neg, abs_inv, abs_pow, abs_of_pos (by linarith : 0 < s + 1), inv_pow]
  have hone : (1 : ℂ) - (r : ℂ) = (r : ℂ) * (s : ℂ) := by
    have hreal : 1 - r = r * s := by
      dsimp [r, d]
      field_simp
      ring
    exact_mod_cast hreal
  have hq (i : ι) : (1 : ℂ) - (r : ℂ) + (r : ℂ) * z i =
      (r : ℂ) * (z i + (s : ℂ)) := by
    rw [hone]
    ring
  have hzi (i : ι) : z i + (s : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [add_re, ofReal_re, zero_re] at hre
    have := hz i
    dsimp only [carlsonRightHalfPlane, Set.mem_ofPred_eq] at this
    linarith
  have hprod :
      (∏ i, ((r : ℂ) * (z i + (s : ℂ))) ^ (-b i)) =
        (r : ℂ) ^ (∑ i, -b i) * ∏ i, (z i + (s : ℂ)) ^ (-b i) := by
    simp_rw [ofReal_mul_cpow hr (hzi _)]
    rw [Finset.prod_mul_distrib, prod_cpow_same_base Finset.univ (r : ℂ) hr0]
  have hexp : (2 : ℂ) + (a' - 1) + (a - 1) + ∑ i, -b i = 0 := by
    rw [Finset.sum_neg_distrib, ← hsum]
    ring
  have hrpow : (r : ℂ) ^ (2 : ℕ) * (r : ℂ) ^ (a' - 1) *
      (r : ℂ) ^ (a - 1) * (r : ℂ) ^ (∑ i, -b i) = 1 := by
    rw [← Complex.cpow_natCast]
    rw [← Complex.cpow_add _ _ hr0, ← Complex.cpow_add _ _ hr0,
      ← Complex.cpow_add _ _ hr0]
    have hexp' : ((2 : ℕ) : ℂ) + (a' - 1) + (a - 1) + ∑ i, -b i = 0 := by
      simpa only [Nat.cast_ofNat] using hexp
    rw [hexp', Complex.cpow_zero]
  rw [habs]
  change (r ^ 2 : ℝ) • _ = _
  rw [Complex.real_smul]
  rw [show ((r ^ 2 : ℝ) : ℂ) = (r : ℂ) ^ (2 : ℕ) by norm_cast]
  change (r : ℂ) ^ (2 : ℕ) *
      (((r : ℂ) ^ (a' - 1) * ((1 : ℂ) - (r : ℂ)) ^ (a - 1)) *
        ∏ i, ((1 : ℂ) - (r : ℂ) + (r : ℂ) * z i) ^ (-b i)) = _
  rw [show
      (fun i => ((1 : ℂ) - (r : ℂ) + (r : ℂ) * z i) ^ (-b i)) =
        fun i => ((r : ℂ) * (z i + (s : ℂ))) ^ (-b i) by
          funext i
          rw [hq i], hprod, hone, Complex.mul_cpow_ofReal_nonneg hr.le hs.le]
  calc
    (r : ℂ) ^ (2 : ℕ) *
        (((r : ℂ) ^ (a' - 1) *
          ((r : ℂ) ^ (a - 1) * (s : ℂ) ^ (a - 1))) *
          ((r : ℂ) ^ (∑ i, -b i) * ∏ i, (z i + (s : ℂ)) ^ (-b i))) =
        ((r : ℂ) ^ (2 : ℕ) * (r : ℂ) ^ (a' - 1) *
          (r : ℂ) ^ (a - 1) * (r : ℂ) ^ (∑ i, -b i)) *
          ((s : ℂ) ^ (a - 1) * ∏ i, (z i + (s : ℂ)) ^ (-b i)) := by ring
    _ = _ := by rw [hrpow, one_mul]

/-- Under the balancing relation, reciprocal translation identifies the positive-ray
integral with the unit-interval integral having its beta exponents interchanged. -/
theorem carlsonRPositiveRayIntegral_eq_unitInterval
    {a a' : ℂ} {b z : ι → ℂ}
    (hsum : a + a' = ∑ i, b i) (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z = carlsonRUnitIntervalIntegral a' a b z := by
  let φ : ℝ → ℝ := fun s => (s + 1)⁻¹
  let φ' : ℝ → ℝ := fun s => -((s + 1) ^ 2)⁻¹
  let g : ℝ → ℂ := fun u =>
    ((u : ℂ) ^ (a' - 1) * (1 - u : ℂ) ^ (a - 1)) *
      ∏ i, ((1 - u : ℂ) + (u : ℂ) * z i) ^ (-b i)
  have hchange := integral_image_eq_integral_abs_deriv_smul
    measurableSet_Ioi
    (fun s hs => (hasDerivAt_recip_add_one s hs).hasDerivWithinAt)
    injOn_recip_add_one g
  rw [show φ '' Set.Ioi 0 = Set.Ioo 0 1 by
      simpa [φ] using image_recip_add_one_Ioi] at hchange
  have hright : (∫ s : ℝ in Set.Ioi 0, |φ' s| • g (φ s)) =
      carlsonRPositiveRayIntegral a b z := by
    unfold carlsonRPositiveRayIntegral
    apply setIntegral_congr_fun measurableSet_Ioi
    intro s hs
    simpa [φ, φ', g] using ray_substitution_point hsum hz hs
  rw [hright] at hchange
  exact hchange.symm.trans <| by
    unfold carlsonRUnitIntervalIntegral
    simp [g]

/-- Carlson's Theorem 6.8-1 in positive-ray form. -/
theorem carlsonRPositiveRayIntegral_eq
    {a a' : ℂ} {b z : ι → ℂ}
    (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hsum : a + a' = ∑ i, b i)
    (hb : b ∈ mvBetaConvergent)
    (hz : z ∈ carlsonRVariableDomain) :
    carlsonRPositiveRayIntegral a b z =
      betaIntegral a a' * carlsonRIntegral (-a') b z := by
  rw [carlsonRPositiveRayIntegral_eq_unitInterval hsum hz]
  rw [carlsonRUnitIntervalIntegral_eq ha' ha (by simpa [add_comm] using hsum) hb hz]
  rw [betaIntegral_symm]

end DirichletTransform

end CarlsonR
