/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.R.Explicit
public import Carlson.R.Homogeneity
public import Carlson.RPolynomial.SharpEstimates
public import Carlson.TwoVariable.RPolynomial
public import ComplexAnalysis.HalfPlane
public import ComplexAnalysis.Pow
public import Dirichlet.Transform.Euler
public import Pochhammer.BinomialSeries
public import ToMathlib.Analysis.SpecialFunctions.Pow

/-!
# The bilateral generating relation and Meixner's formula

Carlson's Generating Relation 6.11-1 expresses a product of powers times an R-function with
transformed nodes as a series of products of two R-polynomials:
`∏ (1 - y zᵢ)^(-bᵢ) R_{-a}(b; (1 - x z)/(1 - y z)) = ∑ (c)ₙ/n! Rₙ(a, c - a; x, y) Rₙ(b, z)`.
It is proved here in regularized form (both sides divided by `Γ(c)`) for arbitrary complex
Dirichlet parameters `b`, in the Euler strip `re a > 0`, `re (c - a) > 0`. The proof
substitutes `t = u x + (1 - u) y` in the generating relation 6.6-1, integrates against the
Euler weight, and interchanges sum and integral using Carlson's estimate 6.2-7(24); the left
side is identified through the single-integral representation of the R-function, with the
principal branches made explicit.

With two nodes and the homogeneity of the R-function on the slit domain, this gives Meixner's
formula (Corollary 6.11-2).

## Main results

* `Carlson.hasSum_bilateral_generating`: Generating Relation 6.11-1.
* `Carlson.hasSum_meixner`: Meixner's formula (Corollary 6.11-2).
* `Carlson.integral_eulerKernel_mul_pow`: the Euler integral of a power of a linear
  interpolation is a two-variable R-polynomial.

## Implementation notes

Carlson removes the conditions on `re a` and `re (c - a)` by analytic continuation; that
extension is not carried out here.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.11.
-/

open Dirichlet
open Complex Set Filter MeasureTheory
open scoped Topology
@[expose] public noncomputable section

namespace Carlson
open TwoVariable

/-- For two right-half-plane numbers `A, P`, the principal powers satisfy
`A^s (P/A)^s = P^s`. -/
theorem cpow_mul_div_cpow_of_re_pos {A P : ℂ} (hA : 0 < A.re) (hP : 0 < P.re) (s : ℂ) :
    A ^ s * (P / A) ^ s = P ^ s := by
  have hA0 : A ≠ 0 := fun h => by simp [h] at hA
  have hP0 : P ≠ 0 := fun h => by simp [h] at hP
  have hargA : |arg A| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hargP : |arg P| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP)
  have hAπ : arg A ≠ Real.pi := fun h => by
    rw [h] at hargA; linarith [abs_lt.mp hargA, Real.pi_pos]
  have hinv : arg A⁻¹ = -arg A := by rw [arg_inv, ite_eq_right_iff.mpr (fun h => absurd h hAπ)]
  have hquot : arg (P / A) = arg P - arg A := by
    rw [div_eq_mul_inv, arg_mul hP0 (inv_ne_zero hA0), hinv, sub_eq_add_neg]
    rw [hinv]
    constructor <;> linarith [abs_lt.mp hargA, abs_lt.mp hargP, Real.pi_pos]
  have hsum : arg A + arg (P / A) ∈ Ioc (-Real.pi) Real.pi := by
    rw [hquot]; constructor <;> linarith [abs_lt.mp hargP, Real.pi_pos]
  have hPA : P / A ≠ 0 := div_ne_zero hP0 hA0
  conv_rhs => rw [show P = A * (P / A) by field_simp]
  rw [cpow_def_of_ne_zero (mul_ne_zero hA0 hPA), log_mul hA0 hPA hsum, add_mul, exp_add,
    ← cpow_def_of_ne_zero hA0, ← cpow_def_of_ne_zero hPA]

/-- The Euler integral of a power of a linear interpolation is a two-variable R-polynomial:
`∫₀¹ u^(a-1) (1-u)^(a'-1) (u x + (1-u) y)ⁿ du = Γ(a) Γ(a') Nₙ(a, a'; x, y) / Γ(a + a' + n)`. -/
theorem integral_eulerKernel_mul_pow {a a' : ℂ} (ha : 0 < a.re) (ha' : 0 < a'.re) (x y : ℂ)
    (n : ℕ) :
    ∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) *
        ((u : ℂ) * x + (1 - u : ℂ) * y) ^ n =
      Gamma a * Gamma a' * (carlsonRPolynomialNumerator₂ n a a' x y *
        (Gamma (a + a' + n))⁻¹) := by
  have hΓ : Gamma a * Gamma a' ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos ha')
  have h1 := regDirichletIntegral_fin_two a a' (fun u : ℝ => ((u : ℂ) * x + (1 - u : ℂ) * y) ^ n)
  rw [regEulerIntegral] at h1
  have h2 : regDirichletIntegral ![a, a'] (fun u => ((u 0 : ℂ) * x + (1 - u 0 : ℂ) * y) ^ n) =
      regCarlsonDirichletAverage (pair a a') (pair x y) (fun w => w ^ n) := by
    unfold regCarlsonDirichletAverage
    apply regDirichletIntegral_congr
    intro u hu
    have hs := (Convexity.StdSimplex.mem_coordinateSet.mp hu).2
    simp only [Fin.sum_univ_two] at hs
    simp only [carlsonAffineForm, Fin.sum_univ_two, pair_zero, pair_one]
    rw [show (u 1 : ℂ) = 1 - u 0 by rw [show u 1 = 1 - u 0 by linarith]; push_cast; ring]
  have hb : pair a a' ∈ mvBetaConvergent := fun i => by fin_cases i <;> simpa
  rw [h2, regCarlsonDirichletAverage_pow n _ hb] at h1
  change regRPolynomial n a a' x y = _ at h1
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma] at h1
  rw [h1, ← mul_assoc, mul_inv_cancel₀ hΓ, one_mul]


variable {ι : Type*} [Fintype ι]

/-- The real binomial series `∑ (B)ₙ sⁿ / n!` converges for `0 ≤ s < 1`. -/
theorem summable_ascPochhammer_real_mul_pow_div_factorial (B : ℝ) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s < 1) :
    Summable (fun n : ℕ => (ascPochhammer ℝ n).eval B / n.factorial * s ^ n) := by
  have h := (hasSum_ascPochhammer_mul_pow_div_factorial (B : ℂ) (s : ℂ)
    (by rw [Complex.norm_real, Real.norm_of_nonneg hs0]; exact hs)).summable
  rw [← Complex.summable_ofReal]
  refine h.congr fun n => ?_
  have hmap : (ascPochhammer ℂ n).eval (B : ℂ) = (((ascPochhammer ℝ n).eval B : ℝ) : ℂ) := by
    rw [← ascPochhammer_map Complex.ofRealHom, Polynomial.eval_map,
      show (B : ℂ) = Complex.ofRealHom B from rfl, Polynomial.eval₂_at_apply]
    rfl
  rw [hmap]; push_cast; ring

/-- **Generating Relation 6.11-1** (bilateral generating relation) in the Euler strip
`re a > 0`, `re (c - a) > 0`, for arbitrary complex Dirichlet parameters `b` with `c = ∑ bᵢ`:
`∏ (1 - y zᵢ)^(-bᵢ) R_{-a}(b; (1 - x z)/(1 - y z)) = ∑ (c)ₙ/n! Rₙ(a, c - a; x, y) Rₙ(b, z)`,
in regularized form (both sides divided by `Γ(c)`), for `‖x zᵢ‖ < 1` and `‖y zᵢ‖ < 1`. -/
theorem hasSum_bilateral_generating (a : ℂ) (b z : ι → ℂ) (x y : ℂ) (ha : 0 < a.re)
    (hca : 0 < (∑ i, b i - a).re) (hx : ∀ i, ‖x * z i‖ < 1) (hy : ∀ i, ‖y * z i‖ < 1) :
    HasSum (fun n : ℕ => carlsonRPolynomialNumerator₂ n a (∑ i, b i - a) x y *
        regCarlsonRPolynomial n b z / n.factorial)
      ((∏ i, (1 - y * z i) ^ (-b i)) *
        regCarlsonR (-a) b (fun i => (1 - x * z i) / (1 - y * z i))) := by
  classical
  set c := ∑ i, b i
  set a' := c - a
  have hΓ : Gamma a * Gamma a' ≠ 0 :=
    mul_ne_zero (Gamma_ne_zero_of_re_pos ha) (Gamma_ne_zero_of_re_pos hca)
  -- radii
  set ρ : ℝ := max ‖x‖ ‖y‖
  set r : ℝ := ((Finset.univ.sup fun i => ‖z i‖₊ : NNReal) : ℝ)
  have hr0 : 0 ≤ r := NNReal.coe_nonneg _
  have hzr : ∀ i, ‖z i‖ ≤ r := fun i => by
    have := Finset.le_sup (f := fun i => ‖z i‖₊) (Finset.mem_univ i)
    exact_mod_cast this
  have hρr : ρ * r < 1 := by
    rcases isEmpty_or_nonempty ι with hι | hι
    · have : r = 0 := by simp [r, Finset.univ_eq_empty]
      rw [this, mul_zero]; exact one_pos
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun i => ‖z i‖₊)
      have hrj : r = ‖z j‖ := by simp only [r, hj, coe_nnnorm]
      rw [hrj]
      show max ‖x‖ ‖y‖ * ‖z j‖ < 1
      rcases le_total ‖x‖ ‖y‖ with h | h
      · rw [max_eq_right h, ← norm_mul]; exact hy j
      · rw [max_eq_left h, ← norm_mul]; exact hx j
  have hρ0 : 0 ≤ ρ := le_max_of_le_left (norm_nonneg _)
  have hρx : ‖x‖ ≤ ρ := le_max_left ‖x‖ ‖y‖
  have hρy : ‖y‖ ≤ ρ := le_max_right ‖x‖ ‖y‖
  -- the interpolated variable
  set T : ℝ → ℂ := fun u => (u : ℂ) * x + (1 - u : ℂ) * y
  have hT : ∀ u ∈ Icc (0 : ℝ) 1, ‖T u‖ ≤ ρ := by
    intro u hu
    calc ‖T u‖ ≤ ‖(u : ℂ) * x‖ + ‖(1 - u : ℂ) * y‖ := norm_add_le _ _
      _ = u * ‖x‖ + (1 - u) * ‖y‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hu.1,
            show (1 - u : ℂ) = ((1 - u : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
            Real.norm_of_nonneg (by linarith [hu.2])]
      _ ≤ u * ρ + (1 - u) * ρ := by
          have h1u : 0 ≤ 1 - u := by linarith [hu.2]
          have := mul_le_mul_of_nonneg_left hρx hu.1
          have := mul_le_mul_of_nonneg_left hρy h1u
          linarith
      _ = ρ := by ring
  have hTz : ∀ u ∈ Icc (0 : ℝ) 1, ∀ i, ‖T u * z i‖ < 1 := fun u hu i => by
    rw [norm_mul]
    calc ‖T u‖ * ‖z i‖ ≤ ρ * r := mul_le_mul (hT u hu) (hzr i) (norm_nonneg _) hρ0
      _ < 1 := hρr
  -- coefficients
  set cf : ℕ → ℂ := fun n => carlsonRPolynomialNumerator n b z / n.factorial
  set B : ℝ := ∑ i, ‖b i‖
  have hcf : ∀ n, ‖cf n‖ * ρ ^ n ≤ (ascPochhammer ℝ n).eval B / n.factorial * (ρ * r) ^ n := by
    intro n
    have h := norm_carlsonRPolynomialNumerator_le_sum_norm n b z hr0 hzr
    simp only [cf, norm_div, Complex.norm_natCast]
    rw [mul_pow, div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right
      (by positivity)]
    calc ‖carlsonRPolynomialNumerator n b z‖ * ρ ^ n
        ≤ (ascPochhammer ℝ n).eval B * r ^ n * ρ ^ n :=
          mul_le_mul_of_nonneg_right h (by positivity)
      _ = _ := by ring
  have hsumm : Summable (fun n => ‖cf n‖ * ρ ^ n) :=
    Summable.of_nonneg_of_le (fun n => by positivity) hcf
      (summable_ascPochhammer_real_mul_pow_div_factorial B (by positivity) hρr)
  -- the Euler weight
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1)
  have hg : IntegrableOn g (Ioo 0 1) := by
    simpa [g] using integrableOn_eulerKernel_mul ha hca (f := fun _ => (1 : ℂ))
      continuousOn_const
  set F : ℕ → ℝ → ℂ := fun n u => g u * (cf n * T u ^ n)
  have hTc : Continuous T := by simp only [T]; fun_prop
  have hFint : ∀ n, Integrable (F n) (volume.restrict (Ioo 0 1)) := by
    intro n
    have := integrableOn_eulerKernel_mul ha hca (f := fun u => cf n * T u ^ n)
      (by fun_prop)
    refine this.congr_fun (fun u _ => ?_) measurableSet_Ioo
    simp only [F, g, mul_assoc]
  have hFnorm : ∀ n, ∫ u in Ioo (0 : ℝ) 1, ‖F n u‖ ≤
      (∫ u in Ioo (0 : ℝ) 1, ‖g u‖) * (‖cf n‖ * ρ ^ n) := by
    intro n
    rw [← integral_mul_const]
    refine setIntegral_mono_on (hFint n).norm (hg.norm.mul_const _) measurableSet_Ioo
      fun u hu => ?_
    simp only [F, norm_mul, norm_pow]
    have := hT u (Ioo_subset_Icc_self hu)
    gcongr
  have hFsum : Summable fun n => ∫ u in Ioo (0 : ℝ) 1, ‖F n u‖ :=
    Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) hFnorm
      (hsumm.mul_left _)
  have hmain := hasSum_integral_of_summable_integral_norm hFint hFsum
  -- identify the sum of the integrals
  have hIn : ∀ n, ∫ u in Ioo (0 : ℝ) 1, F n u = Gamma a * Gamma a' *
      (carlsonRPolynomialNumerator₂ n a a' x y * regCarlsonRPolynomial n b z / n.factorial) := by
    intro n
    have hE := integral_eulerKernel_mul_pow ha hca x y n
    have : ∫ u in Ioo (0 : ℝ) 1, F n u = cf n * ∫ u in Ioo (0 : ℝ) 1,
        (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a' - 1) * ((u : ℂ) * x + (1 - u : ℂ) * y) ^ n := by
      rw [← integral_const_mul]
      congr 1; funext u; simp only [F, g, T]; ring
    rw [this, hE, regCarlsonRPolynomial_eq_numerator_mul_one_div_Gamma,
      show a + a' + (n : ℂ) = c + n by simp only [a']; ring]
    simp only [cf]
    ring
  -- identify the integral of the sum
  have hw : (fun i => (1 - x * z i) / (1 - y * z i)) ∈ carlsonRSlitDomain := by
    intro i
    refine div_mem_slitPlane_of_re_pos ?_ ?_
    · have := hx i
      have h1 := Complex.re_le_norm (x * z i)
      simp only [sub_re, one_re]; linarith
    · have := hy i
      have h1 := Complex.re_le_norm (y * z i)
      simp only [sub_re, one_re]; linarith
  have hR := regCarlsonR_eq_unitIntervalIntegral (t := -a) (b := b) (by simpa using ha)
    (by rw [← sub_eq_add_neg]; exact hca) hw
  rw [neg_neg, show c + -a = a' by simp only [a']; ring] at hR
  have hsumF : ∀ u ∈ Ioo (0 : ℝ) 1, ∑' n, F n u =
      (∏ i, (1 - y * z i) ^ (-b i)) * (g u *
        ∏ i, ((1 - u : ℂ) + (u : ℂ) * ((1 - x * z i) / (1 - y * z i))) ^ (-b i)) := by
    intro u hu
    have hs := hasSum_carlsonRPolynomialNumerator_div_factorial b z (T u)
      (hTz u (Ioo_subset_Icc_self hu))
    have hs' := (hs.mul_left (g u)).tsum_eq
    simp only [F, cf]
    rw [show (fun n => g u * (carlsonRPolynomialNumerator n b z / n.factorial * T u ^ n)) =
      fun n => g u * (carlsonRPolynomialNumerator n b z / (n.factorial : ℂ) * T u ^ n) from rfl,
      hs', carlsonRGeneratingKernel, mul_left_comm, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun i _ => ?_
    have hA : 0 < (1 - y * z i).re := by
      have := hy i; have h1 := Complex.re_le_norm (y * z i)
      simp only [sub_re, one_re]; linarith
    have hP : 0 < (1 - T u * z i).re := by
      have := hTz u (Ioo_subset_Icc_self hu) i; have h1 := Complex.re_le_norm (T u * z i)
      simp only [sub_re, one_re]; linarith
    have hA0 : (1 - y * z i) ≠ 0 := fun h => by simp [h] at hA
    have hq : (1 - u : ℂ) + (u : ℂ) * ((1 - x * z i) / (1 - y * z i)) =
        (1 - T u * z i) / (1 - y * z i) := by
      rw [eq_div_iff hA0, add_mul, mul_assoc, div_mul_cancel₀ _ hA0]
      simp only [T]; ring
    rw [hq, cpow_mul_div_cpow_of_re_pos hA hP, one_div, ← cpow_neg]
  have hint : ∫ u in Ioo (0 : ℝ) 1, ∑' n, F n u = Gamma a * Gamma a' *
      ((∏ i, (1 - y * z i) ^ (-b i)) *
        regCarlsonR (-a) b (fun i => (1 - x * z i) / (1 - y * z i))) := by
    rw [setIntegral_congr_fun measurableSet_Ioo hsumF, integral_const_mul, hR,
      carlsonRUnitIntervalIntegral]
    have key : ∀ I P : ℂ, P * I = Gamma a * Gamma a' * (P * ((Gamma a)⁻¹ * (Gamma a')⁻¹ * I)) := by
      intro I P
      field_simp [Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hca]
    exact key _ _
  rw [hint] at hmain
  simp_rw [hIn] at hmain
  have := hmain.mul_left (Gamma a * Gamma a')⁻¹
  simp only [← mul_assoc, inv_mul_cancel₀ hΓ, one_mul] at this
  exact this


/-- The principal argument of a quotient of right-half-plane numbers is the difference of
their arguments. -/
theorem arg_div_of_re_pos {P A : ℂ} (hP : 0 < P.re) (hA : 0 < A.re) :
    arg (P / A) = arg P - arg A := by
  have hA0 : A ≠ 0 := fun h => by simp [h] at hA
  have hP0 : P ≠ 0 := fun h => by simp [h] at hP
  have hargA : |arg A| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA)
  have hargP : |arg P| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP)
  have hAπ : arg A ≠ Real.pi := fun h => by
    rw [h] at hargA; linarith [abs_lt.mp hargA, Real.pi_pos]
  have hinv : arg A⁻¹ = -arg A := by rw [arg_inv, ite_eq_right_iff.mpr (fun h => absurd h hAπ)]
  rw [div_eq_mul_inv, arg_mul hP0 (inv_ne_zero hA0), hinv, sub_eq_add_neg]
  rw [hinv]
  constructor <;> linarith [abs_lt.mp hargA, abs_lt.mp hargP, Real.pi_pos]

/-- **Meixner's formula** (Corollary 6.11-2) in regularized form, in the Euler strip
`re a > 0`, `re (c - a) > 0`, for `‖xX‖, ‖xY‖, ‖yX‖, ‖yY‖ < 1`:
`(1 - yX)^(a-β) (1 - yY)^(a+β-c) R_{-a}(β, c-β; (1-xX)(1-yY), (1-xY)(1-yX))
  = ∑ (c)ₙ/n! Rₙ(a, c-a; x, y) Rₙ(β, c-β; X, Y)`. -/
theorem hasSum_meixner (a β c x y X Y : ℂ) (ha : 0 < a.re) (hca : 0 < (c - a).re)
    (hxX : ‖x * X‖ < 1) (hxY : ‖x * Y‖ < 1) (hyX : ‖y * X‖ < 1) (hyY : ‖y * Y‖ < 1) :
    HasSum (fun n : ℕ => carlsonRPolynomialNumerator₂ n a (c - a) x y *
        regRPolynomial n β (c - β) X Y / n.factorial)
      ((1 - y * X) ^ (a - β) * (1 - y * Y) ^ (a + β - c) *
        regCarlsonR (-a) (pair β (c - β))
          (pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X)))) := by
  have hsum : ∑ i, pair β (c - β) i = c := by simp [pair, Fin.sum_univ_two]
  have h := hasSum_bilateral_generating a (pair β (c - β)) (pair X Y) x y ha
    (by rw [hsum]; exact hca) (fun i => by fin_cases i; exacts [hxX, hxY])
    (fun i => by fin_cases i; exacts [hyX, hyY])
  rw [hsum] at h
  set A₀ := 1 - y * X
  set A₁ := 1 - y * Y
  have hA₀ : 0 < A₀.re := Complex.re_one_sub_pos hyX
  have hA₁ : 0 < A₁.re := Complex.re_one_sub_pos hyY
  have hP₀ : 0 < (1 - x * X).re := Complex.re_one_sub_pos hxX
  have hP₁ : 0 < (1 - x * Y).re := Complex.re_one_sub_pos hxY
  have hA₀0 : A₀ ≠ 0 := fun h => by simp [h] at hA₀
  have hA₁0 : A₁ ≠ 0 := fun h => by simp [h] at hA₁
  set μ := A₀ * A₁
  set w : Fin 2 → ℂ := fun i => (1 - x * pair X Y i) / (1 - y * pair X Y i)
  have hw : w ∈ carlsonRSlitDomain := by
    intro i; fin_cases i
    · exact div_mem_slitPlane_of_re_pos hP₀ hA₀
    · exact div_mem_slitPlane_of_re_pos hP₁ hA₁
  have hμ : μ ∈ slitPlane := mul_mem_slitPlane_of_re_pos hA₀ hA₁
  have hargA₀ : |arg A₀| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA₀)
  have hargA₁ : |arg A₁| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA₁)
  have hargP₀ : |arg (1 - x * X)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP₀)
  have hargP₁ : |arg (1 - x * Y)| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hP₁)
  have hargμ : arg μ = arg A₀ + arg A₁ := by
    refine arg_mul hA₀0 hA₁0 ⟨?_, ?_⟩ <;>
      linarith [abs_lt.mp hargA₀, abs_lt.mp hargA₁, Real.pi_pos]
  have hharg : ∀ i, arg μ + arg (w i) ∈ Set.Ioo (-Real.pi) Real.pi := by
    intro i; fin_cases i
    · change arg μ + arg ((1 - x * X) / A₀) ∈ _
      rw [arg_div_of_re_pos hP₀ hA₀, hargμ]
      constructor <;> linarith [abs_lt.mp hargA₁, abs_lt.mp hargP₀, Real.pi_pos]
    · change arg μ + arg ((1 - x * Y) / A₁) ∈ _
      rw [arg_div_of_re_pos hP₁ hA₁, hargμ]
      constructor <;> linarith [abs_lt.mp hargA₀, abs_lt.mp hargP₁, Real.pi_pos]
  have hhom := regCarlsonR_mul_of_arg_add (-a) (pair β (c - β)) hw hμ hharg
  have hnodes : (fun i => μ * w i) =
      pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X)) := by
    funext i; fin_cases i
    · change μ * ((1 - x * X) / A₀) = (1 - x * X) * A₁
      simp only [μ]; field_simp
    · change μ * ((1 - x * Y) / A₁) = (1 - x * Y) * A₀
      simp only [μ]; field_simp
  rw [hnodes] at hhom
  have hμ0 : μ ≠ 0 := mul_ne_zero hA₀0 hA₁0
  have hR : regCarlsonR (-a) (pair β (c - β)) w = μ ^ a *
      regCarlsonR (-a) (pair β (c - β))
        (pair ((1 - x * X) * (1 - y * Y)) ((1 - x * Y) * (1 - y * X))) := by
    rw [hhom, ← mul_assoc, ← cpow_add _ _ hμ0, add_neg_cancel, cpow_zero, one_mul]
  have hpre : (∏ i, (1 - y * pair X Y i) ^ (-pair β (c - β) i)) * μ ^ a =
      A₀ ^ (a - β) * A₁ ^ (a + β - c) := by
    rw [Fin.prod_univ_two, mul_cpow_of_re_pos hA₀ hA₁]
    simp only [pair_zero, pair_one]
    rw [show a - β = -β + a by ring, show a + β - c = -(c - β) + a by ring,
      cpow_add _ _ hA₀0, cpow_add _ _ hA₁0]
    ring
  change HasSum _ ((∏ i, (1 - y * pair X Y i) ^ (-pair β (c - β) i)) *
    regCarlsonR (-a) (pair β (c - β)) w) at h
  rw [hR, ← mul_assoc, hpre] at h
  exact h

end Carlson
