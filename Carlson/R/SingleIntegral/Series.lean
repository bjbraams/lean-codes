/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.SlitPlane
public import Carlson.R.Continuation
public import Carlson.RPolynomial.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Pochhammer.Gamma
public import Pochhammer.BinomialSeries
public import Carlson.RPolynomial.PowerSeries
public import Carlson.R.Deriv
public import Carlson.R.Relations
public import Carlson.RPolynomial.Generating

/-!
# Unit-interval kernel and near-one series representation

The beta-weighted unit-interval integral of Carlson's single-integral representation
(Theorem 6.8-1), and the R-polynomial series expansion of the regularized R-integral near the
all-one node vector, which identifies the two in a polydisc around that point.

## Main definitions

* `Carlson.carlsonRUnitIntervalIntegral`: the unit-interval integral with beta weight.

## Main results

* `Carlson.hasSum_regCarlsonRIntegral_near_one`: the R-polynomial expansion of the regularized
  R-integral near the all-one node vector.
* `Carlson.carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one`: Carlson's single-integral
  identity in that polydisc.

## References

* [Carl77] B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977.
-/

open Dirichlet
open Complex MeasureTheory ProbabilityTheory Filter Set
open scoped Topology
@[expose] public noncomputable section
namespace Carlson
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

/-- A beta kernel times a power of the variable is a beta kernel with shifted first exponent. -/
private lemma betaKernel_mul_pow_eq {a a' : ℂ} (c : ℂ) (n : ℕ) {u : ℝ} (hu : u ∈ Set.Ioo 0 1) :
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * (c * (u : ℂ) ^ n) =
      c * ((u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1)) := by
  have hu0 : (u : ℂ) ≠ 0 := ofReal_ne_zero.mpr hu.1.ne'
  calc
    (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * (c * (u : ℂ) ^ n) =
        c * (((u : ℂ) ^ (a - 1) * (u : ℂ) ^ n) * (1 - u : ℂ) ^ (a' - 1)) := by ring
    _ = c * ((u : ℂ) ^ ((a - 1) + n) * (1 - u : ℂ) ^ (a' - 1)) := by
      rw [← Complex.cpow_natCast, Complex.cpow_add _ _ hu0]
    _ = c * ((u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1)) := by
      congr 3
      ring

/-- A beta kernel times a monomial is integrable on the open unit interval. -/
private lemma integrable_betaKernel_mul_pow {a a' : ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re)
    (c : ℂ) (n : ℕ) :
    Integrable (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * (c * (u : ℂ) ^ n))
      (volume.restrict (Set.Ioo 0 1)) := by
  have han : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
  have hbase : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (a + n - 1) * (1 - u : ℂ) ^ (a' - 1))
      (Set.Ioo 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent han ha')
  exact (hbase.const_mul c).congr <| by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (betaKernel_mul_pow_eq c n hu).symm

/-- Integrating a beta kernel against a monomial gives a beta integral with shifted first
exponent. -/
private lemma integral_betaKernel_mul_pow {a a' : ℂ} (c : ℂ) (n : ℕ) :
    ∫ u in Set.Ioo (0 : ℝ) 1, (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * (c * (u : ℂ) ^ n) =
      c * betaIntegral (a + n) a' := by
  rw [betaIntegral, intervalIntegral.integral_of_le zero_le_one,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  exact betaKernel_mul_pow_eq c n hu

/-- Near the all-one Carlson variable, the unit-interval integral is the termwise beta
integral of the generating series for the R-polynomials. The proof integrates the generating
series term by term, dominated by the beta kernel times the summable coefficient norms. -/
private lemma hasSum_carlsonRUnitIntervalIntegral
    (a a' : ℂ) (b y : ι → ℂ) (ha : 0 < a.re) (ha' : 0 < a'.re)
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (fun n : ℕ =>
      carlsonRPolynomialNumerator n b y / (n.factorial : ℂ) *
        betaIntegral (a + n) a')
      (carlsonRUnitIntervalIntegral a a' b (fun i => 1 - y i)) := by
  let K : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)
  let A : ℕ → ℂ := fun n => carlsonRPolynomialNumerator n b y / (n.factorial : ℂ)
  let F : ℕ → ℝ → ℂ := fun n u => K u * (A n * (u : ℂ) ^ n)
  let B : ℕ → ℝ → ℝ := fun n u => ‖A n‖ * ‖K u‖
  have hAsum : Summable A := by
    simpa [A] using summable_carlsonRPolynomialNumerator_div_factorial b y 1 (by simpa using hy)
  have hKint : Integrable K (volume.restrict (Set.Ioo 0 1)) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le zero_le_one).mp (betaIntegral_convergent ha ha')
  have hBsum : ∀ᵐ u ∂(volume.restrict (Set.Ioo 0 1)), Summable fun n => B n u := by
    filter_upwards with u
    exact hAsum.norm.mul_right _
  have hBint : Integrable (fun u => ∑' n, B n u) (volume.restrict (Set.Ioo 0 1)) := by
    have heq : (fun u => ∑' n, B n u) = fun u => (∑' n, ‖A n‖) * ‖K u‖ := by
      funext u
      simp only [B]
      rw [tsum_mul_right]
    rw [heq]
    exact hKint.norm.const_mul _
  have hbound (n : ℕ) : ∀ᵐ u ∂(volume.restrict (Set.Ioo 0 1)), ‖F n u‖ ≤ B n u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    simp only [F, B, norm_mul]
    have hu_norm : ‖(u : ℂ)‖ ≤ 1 := by
      simp only [norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact hu.2.le
    rw [norm_pow]
    calc
      ‖K u‖ * (‖A n‖ * ‖(u : ℂ)‖ ^ n) ≤ ‖K u‖ * (‖A n‖ * 1 ^ n) := by
        gcongr
      _ = ‖A n‖ * ‖K u‖ := by ring
  have hlim : ∀ᵐ u ∂(volume.restrict (Set.Ioo 0 1)),
      HasSum (fun n => F n u) (K u * ∏ i, (1 - (u : ℂ) * y i) ^ (-b i)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    exact (hasSum_singleIntegral_kernel b y hu.1.le hu.2.le hy).mul_left (K u)
  have hseries := hasSum_integral_of_dominated_convergence B
    (fun n => (integrable_betaKernel_mul_pow ha ha' (A n) n).aestronglyMeasurable) hbound hBsum
    hBint hlim
  simp only [integral_betaKernel_mul_pow] at hseries
  convert hseries using 1
  unfold carlsonRUnitIntervalIntegral K
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  ring

/-- The regularized R-integral has its R-polynomial expansion near the all-one variable. -/
theorem hasSum_regCarlsonRIntegral_near_one
    (a : ℂ) (b y : ι → ℂ) (hb : b ∈ mvBetaConvergent)
    (hy : ∀ i, ‖y i‖ < 1) :
    HasSum (fun n : ℕ =>
      (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * regCarlsonRPolynomial n b y)
      (regCarlsonRIntegral (-a) b (fun i => 1 - y i)) := by
  let coeff : ℕ → ℂ := fun n =>
    (-1 : ℂ) ^ n * ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ))
  let M : ℕ → ℝ := fun n =>
    ‖(ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * ((‖y‖ : ℂ) ^ n)‖
  have hynorm : ‖y‖ < 1 := (pi_norm_lt_iff zero_lt_one).2 hy
  have hM : Summable M := by
    simpa [M] using summable_norm_ascPochhammer_mul_pow_div_factorial a (‖y‖ : ℂ)
      (by simpa using hynorm)
  have hbound : ∀ n u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
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
  have hpoint : ∀ u, u ∈ Convexity.StdSimplex.coordinateSet ℝ ι →
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
      regCarlsonRPolynomial n b (shiftCarlsonVariables 1 (fun i => 1 - y i))) =
      fun n => (ascPochhammer ℂ n).eval a / (n.factorial : ℂ) *
        regCarlsonRPolynomial n b y := by
    funext n
    rw [hshift, regCarlsonRPolynomial_smul_of_mem_mvBetaConvergent n (-1) y hb]
    simp only [coeff]
    ring_nf
    rw [show n * 2 = 2 * n by omega, pow_mul]
    simp
  rw [hterms] at hs
  simpa [regCarlsonRIntegral] using hs

/-- Carlson's single-integral identity in the polydisc centered at the all-one variable. -/
lemma carlsonRUnitIntervalIntegral_eq_of_norm_one_sub_lt_one
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
        ((ascPochhammer ℂ n).eval a / (n.factorial : ℂ) * regCarlsonRPolynomial n b y) := by
    funext n
    rw [regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma]
    rw [← hsum]
    rw [betaIntegral_add_nat_left a a' n ha ha']
    ring
  rw [hterms] at hunit
  exact hunit.unique (by
    simpa [carlsonRIntegral, mul_assoc] using hr)

end Carlson
