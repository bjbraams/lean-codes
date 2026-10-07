/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.GegenbauerProductComplex
public import Carlson.Jacobi.Gegenbauer
public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Carlson.RPolynomial.GeneratingIdentities
public import Carlson.TwoVariable.R.ElementaryValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Carlson.Jacobi.GegenbauerAddition
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Pochhammer.Identities
public import Carlson.Jacobi.ChebyshevU
public import Carlson.Jacobi.RPolynomialExercises
public import Carlson.TwoVariable.QuadraticSlit
public import Carlson.R.IntegerParameters
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Carlson.Jacobi.Rodrigues
public import Carlson.Jacobi.Endpoints
public import Carlson.Jacobi.EndpointRodrigues

/-!
# Gegenbauer, Chebyshev and Legendre exercises (Chapters 6 and 7)

Exercises of Carlson's Chapters 6 and 7 on Gegenbauer, Chebyshev and Legendre polynomials,
derived from the R-polynomial representation
`n! Cₙ^ν((w + w⁻¹)/2) = Nₙ(ν, ν; w, w⁻¹)` and the Gegenbauer generating function.

## Main results

* `eval_gegenbauer_add_param`: `C_n^{λ+μ} = ∑ₘ Cₘ^λ C_{n-m}^μ` (from Exercise 6.6-7).
* `sum_legendre_cos_mul_legendre_cos`: Exercise 6.7-7.
* `eval_gegenbauer_cos_two_mul`: Exercise 6.7-8.
* `gegenbauer_tobey`: Exercise 6.7-11.
* `eval_gegenbauer_neg`, `eval_legendre_one`: Exercise 6.7-1.
* `chebyshevU_cos_eq_numerator`: Exercise 6.7-3.
* `hasSum_chebyshevT_log`: Exercise 6.7-4.
* `unsold`: Unsöld's theorem, Exercise 7.3-1.
* `hasSum_gegenbauer_dist`: the expansion of `‖x - y‖^{-2ν}` in an inner product space,
  Exercise 6.7-12.
* `hasSum_inv_dist_spherical`: Exercise 7.3-2.
* `factorial_mul_eval_gegenbauer_affine`: the binomial theorem for Gegenbauer polynomials.
* `eval_gegenbauer_cos_rainville`: Exercise 6.7-9 (division-free form).
* `eval_legendre_cos_eq_sum`, `sin_pow_mul_eval_legendre_sin`: Exercise 6.7-10.
* `eval_gegenbauer_two_mul_eq_hypergeometric`, `eval_gegenbauer_two_mul_add_one_eq_hypergeometric`:
  Exercise 6.9-9.
* `cos_two_mul_mul_eq_hypergeometric_cos`, `cos_two_mul_mul_eq_hypergeometric_sin`,
  `cos_two_mul_add_one_mul_eq_hypergeometric_cos`, `cos_two_mul_add_one_mul_eq_hypergeometric_sin`:
  Exercise 6.9-10.
* `sin_two_mul_succ_mul_eq_hypergeometric_sin`, `sin_two_mul_succ_mul_eq_hypergeometric_cos`,
  `sin_two_mul_add_one_mul_eq_hypergeometric_sin`, `sin_two_mul_add_one_mul_eq_hypergeometric_cos`:
  Exercise 6.9-11.
* `ascPochhammer_mul_eval_gegenbauer_reflect`: Exercise 6.10-7.
* `carlsonRPolynomialNumerator₂_neg_sub_sq`: Exercise 6.10-8.
* `carlsonRPolynomial_fib`: Exercise 6.10-9 for the Fibonacci numbers.
* `eval_gegenbauer_eq_hypergeometric`: Exercise 6.10-10.
* `two_pow_mul_carlsonRPolynomial_cos`: Exercise 6.10-11.
* `regCarlsonR_one_half_sub_pair_sq`, `regCarlsonR_neg_one_half_sub_pair_sq`,
  `carlsonR_one_half_sub_pair_sq`: Exercise 6.10-12.
* `factorial_mul_eval_gegenbauer_two_mul_cos_half`,
  `factorial_mul_eval_gegenbauer_two_mul_add_one_cos_half`: Exercise 7.1-12.
* `circleIntegral_gegenbauer_mul_jacobiSecondKind`: Exercise 7.2-1.
* `iterate_derivative_X_sq_sub_one_pow`, `iteratedDeriv_gegenbauer_rodrigues`: Rodrigues'
  formulas for Legendre and Gegenbauer polynomials, Exercise 7.8-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Chapters 6 and 7.
-/

open Complex Polynomial Finset

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- `Cₙ^ν((w + w⁻¹)/2) = Nₙ(ν, ν; w, w⁻¹)/n!`. -/
theorem eval_gegenbauer_eq_numerator (ν : ℂ) {w : ℂ} (hw : w ≠ 0) (n : ℕ) :
    (gegenbauer ν n).eval ((w + w⁻¹) / 2) =
      carlsonRPolynomialNumerator₂ n ν ν w w⁻¹ / n.factorial := by
  rw [← factorial_mul_eval_gegenbauer ν w hw n]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Addition of Gegenbauer parameters** (from Exercise 6.6-7):
`C_n^{λ+μ}(x) = ∑ₘ Cₘ^λ(x) C_{n-m}^μ(x)`. -/
theorem eval_gegenbauer_add_param (lam μ x : ℂ) (n : ℕ) :
    (gegenbauer (lam + μ) n).eval x = ∑ m ∈ range (n + 1),
      (gegenbauer lam m).eval x * (gegenbauer μ (n - m)).eval x := by
  obtain ⟨w, hw, rfl⟩ := exists_add_inv_div_two x
  simp only [eval_gegenbauer_eq_numerator _ hw]
  have h := carlsonRPolynomialNumerator_add_params n (pair lam lam) (pair μ μ) (pair w w⁻¹)
  have hp : pair lam lam + pair μ μ = pair (lam + μ) (lam + μ) := by
    funext i; fin_cases i <;> rfl
  rw [hp] at h
  simpa only [carlsonRPolynomialNumerator_pair] using h

/-- **Exercise 6.7-7** in polynomial form: `∑ₘ Pₘ(x) P_{n-m}(x) = Uₙ(x)`. -/
theorem sum_legendre_mul_legendre (x : ℂ) (n : ℕ) :
    ∑ m ∈ range (n + 1), (gegenbauer (1 / 2 : ℂ) m).eval x *
      (gegenbauer (1 / 2 : ℂ) (n - m)).eval x = (Chebyshev.U ℂ n).eval x := by
  rw [← eval_gegenbauer_add_param, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    gegenbauer_one_param_eq_chebyshev_U]

/-- **Exercise 6.7-7**: `∑ₘ Pₘ(cos θ) P_{n-m}(cos θ) = sin((n + 1)θ)/sin θ` when `sin θ ≠ 0`. -/
theorem sum_legendre_cos_mul_legendre_cos (θ : ℂ) (hθ : sin θ ≠ 0) (n : ℕ) :
    ∑ m ∈ range (n + 1), (gegenbauer (1 / 2 : ℂ) m).eval (cos θ) *
      (gegenbauer (1 / 2 : ℂ) (n - m)).eval (cos θ) = sin ((n + 1) * θ) / sin θ := by
  rw [sum_legendre_mul_legendre, eq_div_iff hθ]
  have := Chebyshev.U_complex_cos θ n
  push_cast at this
  exact this

/-- **Exercise 6.7-8** in polynomial form: `C_n^ν(2x² - 1) = ∑ₘ (-1)ᵐ Cₘ^ν(x) C_{2n-m}^ν(x)`;
with `x = cos θ` this is `C_n^ν(cos 2θ)`. -/
theorem eval_gegenbauer_two_mul_sq_sub_one (ν x : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval (2 * x ^ 2 - 1) = ∑ m ∈ range (2 * n + 1),
      (-1) ^ m * (gegenbauer ν m).eval x * (gegenbauer ν (2 * n - m)).eval x := by
  obtain ⟨w, hw, rfl⟩ := exists_add_inv_div_two x
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hx : 2 * ((w + w⁻¹) / 2) ^ 2 - 1 = (w ^ 2 + (w ^ 2)⁻¹) / 2 := by
    field_simp; ring
  rw [hx]
  simp only [eval_gegenbauer_eq_numerator _ hw, eval_gegenbauer_eq_numerator _ hw2]
  have h := carlsonRPolynomialNumerator_sq_nodes n (pair ν ν) (pair w w⁻¹)
  have hp : (fun i => pair w w⁻¹ i ^ 2) = pair (w ^ 2) (w ^ 2)⁻¹ := by
    funext i; fin_cases i <;> simp [pair]
  rw [hp] at h
  simp only [carlsonRPolynomialNumerator_pair] at h
  rw [h]

/-- **Exercise 6.7-8**: `C_n^ν(cos 2θ) = ∑ₘ (-1)ᵐ Cₘ^ν(cos θ) C_{2n-m}^ν(cos θ)`. -/
theorem eval_gegenbauer_cos_two_mul (ν θ : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval (cos (2 * θ)) = ∑ m ∈ range (2 * n + 1),
      (-1) ^ m * (gegenbauer ν m).eval (cos θ) * (gegenbauer ν (2 * n - m)).eval (cos θ) := by
  rw [cos_two_mul, eval_gegenbauer_two_mul_sq_sub_one]

/-- **Exercise 6.7-11** (Tobey):
`(n + 1) C_{n+1}^ν(cos θ) = 2ν ∑_{m ≤ n} Cₘ^ν(cos θ) cos((n + 1 - m)θ)`. -/
theorem gegenbauer_tobey (ν θ : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (gegenbauer ν (n + 1)).eval (cos θ) =
      2 * ν * ∑ m ∈ range (n + 1), (gegenbauer ν m).eval (cos θ) *
        cos (((n + 1 - m : ℕ) : ℂ) * θ) := by
  set w := exp (θ * I)
  have hw : w ≠ 0 := exp_ne_zero _
  have hc : cos θ = (w + w⁻¹) / 2 := by
    rw [Complex.cos, ← exp_neg, show -θ * I = -(θ * I) by ring]
  have hcos : ∀ k : ℕ, cos ((k : ℂ) * θ) = (w ^ k + w⁻¹ ^ k) / 2 := fun k => by
    have hwinv : w⁻¹ = exp (-(θ * I)) := (exp_neg _).symm
    rw [hwinv, ← exp_nat_mul, ← exp_nat_mul, Complex.cos]; ring_nf
  rw [hc]
  simp only [eval_gegenbauer_eq_numerator _ hw]
  have h := carlsonRPolynomialNumerator_tobey n (pair ν ν) (pair w w⁻¹)
  simp only [carlsonRPolynomialNumerator_pair, Fin.sum_univ_two, pair_zero, pair_one] at h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [Nat.factorial_succ]
  push_cast
  rw [show ((n : ℂ) + 1) * (carlsonRPolynomialNumerator₂ (n + 1) ν ν w w⁻¹ /
    (((n : ℂ) + 1) * n.factorial)) = carlsonRPolynomialNumerator₂ (n + 1) ν ν w w⁻¹ /
      n.factorial by field_simp, h, mul_sum]
  refine sum_congr rfl fun m _ => ?_
  rw [hcos]
  ring

/-- **Exercise 6.7-1**, parity: `C_n^ν(-x) = (-1)ⁿ C_n^ν(x)`. -/
theorem eval_gegenbauer_neg (ν x : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval (-x) = (-1) ^ n * (gegenbauer ν n).eval x := by
  obtain ⟨w, hw, rfl⟩ := exists_add_inv_div_two x
  have hw' : -w ≠ 0 := neg_ne_zero.mpr hw
  rw [show -((w + w⁻¹) / 2) = (-w + (-w)⁻¹) / 2 by rw [inv_neg]; ring,
    eval_gegenbauer_eq_numerator _ hw', eval_gegenbauer_eq_numerator _ hw]
  have h := carlsonRPolynomialNumerator₂_smul n ν ν (-1) w w⁻¹
  rw [show (-1 : ℂ) * w = -w by ring, show (-1 : ℂ) * w⁻¹ = (-w)⁻¹ by rw [inv_neg]; ring] at h
  rw [h]; ring

/-- **Exercise 6.7-1**: `Pₙ(1) = 1` and `Pₙ(-x) = (-1)ⁿ Pₙ(x)`. -/
theorem eval_legendre_one (n : ℕ) : (gegenbauer (1 / 2 : ℂ) n).eval 1 = 1 := by
  rw [eval_gegenbauer_one, show 2 * (1 / 2 : ℂ) = 1 by norm_num, ascPochhammer_eval_one]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.7-3**: `Uₙ(cos θ) = (n + 1) Rₙ(1, 1; e^{iθ}, e^{-iθ})`, i.e.
`Nₙ(1, 1; e^{iθ}, e^{-iθ})/n! = Uₙ(cos θ)`, and `Uₙ(cos θ) sin θ = sin((n + 1)θ)`. -/
theorem chebyshevU_cos_eq_numerator (θ : ℂ) (n : ℕ) :
    (Chebyshev.U ℂ n).eval (cos θ) =
      carlsonRPolynomialNumerator₂ n 1 1 (exp (θ * I)) (exp (-θ * I)) / n.factorial ∧
    (Chebyshev.U ℂ n).eval (cos θ) * sin θ = sin ((n + 1) * θ) := by
  refine ⟨?_, by have := Chebyshev.U_complex_cos θ n; push_cast at this; exact this⟩
  have hw : exp (θ * I) ≠ 0 := exp_ne_zero _
  have hc : cos θ = (exp (θ * I) + (exp (θ * I))⁻¹) / 2 := by
    rw [Complex.cos, ← exp_neg, show -θ * I = -(θ * I) by ring]
  rw [← gegenbauer_one_param_eq_chebyshev_U, hc, eval_gegenbauer_eq_numerator _ hw,
    ← exp_neg, show -(θ * I) = -θ * I by ring]

/-- **Exercise 6.7-4**: `-½ log(1 - 2t cos θ + t²) = ∑_{n ≥ 1} tⁿ/n Tₙ(cos θ)` for
`|t| < e^{-|Im θ|}`, written with the two conditions `|t e^{±iθ}| < 1`. -/
theorem hasSum_chebyshevT_log (θ t : ℂ) (h₁ : ‖t * exp (θ * I)‖ < 1)
    (h₂ : ‖t * exp (-θ * I)‖ < 1) :
    HasSum (fun n : ℕ => t ^ n / n * (Chebyshev.T ℂ n).eval (cos θ))
      (-(1 / 2) * log (1 - 2 * t * cos θ + t ^ 2)) := by
  have hA := hasSum_taylorSeries_neg_log h₁
  have hB := hasSum_taylorSeries_neg_log h₂
  have hre : ∀ u : ℂ, ‖u‖ < 1 → 0 < (1 - u).re := fun u hu => by
    have := (abs_re_le_norm u).trans_lt hu
    simp only [sub_re, one_re]; linarith [le_abs_self u.re]
  have hlog : log (1 - 2 * t * cos θ + t ^ 2) =
      log (1 - t * exp (θ * I)) + log (1 - t * exp (-θ * I)) := by
    rw [← log_mul_of_re_pos (hre _ h₁) (hre _ h₂)]
    congr 1
    rw [Complex.cos]
    have he : exp (θ * I) * exp (-θ * I) = 1 := by rw [← exp_add]; ring_nf; exact exp_zero
    linear_combination (-t ^ 2) * he
  rw [hlog]
  have h := (hA.add hB).div_const 2
  rw [show (-log (1 - t * exp (θ * I)) + -log (1 - t * exp (-θ * I))) / 2 =
    -(1 / 2) * (log (1 - t * exp (θ * I)) + log (1 - t * exp (-θ * I))) by ring] at h
  refine h.congr_fun fun n => ?_
  rw [Chebyshev.T_complex_cos, Complex.cos]
  simp only [Int.cast_natCast]
  rw [mul_pow, mul_pow, ← exp_nat_mul, ← exp_nat_mul]
  ring_nf
/-- **Exercise 7.3-1** (Unsöld's theorem): `∑_{m=-n}^{n} (-1)ᵐ P_n^m(x) P_n^{-m}(x) = 1`, with
`x = cos θ` for any complex `θ`. -/
theorem unsold (n : ℕ) (θ : ℂ) :
    ∑ m ∈ Finset.Icc (-(n : ℤ)) n, (-1) ^ m * assocLegendreInt n m θ *
      assocLegendreInt n (-m) θ = 1 := by
  have h := legendre_addition_exp n θ θ 0
  simp only [mul_zero, zero_mul, exp_zero, mul_one, cos_zero] at h
  rw [← h, show cos θ * cos θ + sin θ * sin θ = 1 by rw [← sq, ← sq, cos_sq_add_sin_sq],
    eval_legendre_one]

/-- The generating function at a real point `c ∈ [-1, 1]` and real `0 ≤ t < 1`:
`(1 - 2ct + t²)^{-ν} = ∑ Cₙ^ν(c) tⁿ`. -/
theorem hasSum_gegenbauer_real (ν : ℂ) {c t : ℝ} (hc : |c| ≤ 1) (ht0 : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun n : ℕ => (gegenbauer ν n).eval (c : ℂ) * (t : ℂ) ^ n)
      (((1 - 2 * c * t + t ^ 2 : ℝ) : ℂ) ^ (-ν)) := by
  set s : ℝ := Real.sqrt (1 - c ^ 2)
  have hs2 : s ^ 2 = 1 - c ^ 2 := Real.sq_sqrt (by nlinarith [abs_le.mp hc])
  set w : ℂ := c + s * I
  have hnw : ‖w‖ = 1 := by
    rw [show w = ((c : ℂ) + (s : ℂ) * I) from rfl, Complex.norm_add_mul_I,
      show c ^ 2 + s ^ 2 = 1 by linarith, Real.sqrt_one]
  have hw : w ≠ 0 := fun h => by rw [h, norm_zero] at hnw; exact zero_ne_one hnw
  have hcs : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast (by linarith : c ^ 2 + s ^ 2 = 1)
  have hwinv : w⁻¹ = c - s * I := by
    rw [inv_eq_of_mul_eq_one_right]
    simp only [w]; ring_nf; rw [I_sq]; linear_combination hcs
  have hnwi : ‖w⁻¹‖ = 1 := by rw [norm_inv, hnw, inv_one]
  have htn : ‖(t : ℂ)‖ = t := by rw [Complex.norm_real, Real.norm_of_nonneg ht0]
  have h := hasSum_gegenbauer_mul_pow ν w t hw (by rw [norm_mul, htn, hnw, mul_one]; exact ht1)
    (by rw [norm_mul, htn, hnwi, mul_one]; exact ht1)
  have hx : (w + w⁻¹) / 2 = c := by rw [hwinv]; simp only [w]; ring
  rw [hx] at h
  have hct : t * c < 1 := by
    have := abs_le.mp hc
    nlinarith
  have hre1 : 0 < (1 - (t : ℂ) * w).re := by simp [w]; linarith
  have hre2 : 0 < (1 - (t : ℂ) * w⁻¹).re := by rw [hwinv]; simp; linarith
  rw [← mul_cpow_of_re_pos hre1 hre2] at h
  convert h using 2
  rw [show (1 - (t : ℂ) * w) * (1 - t * w⁻¹) = 1 - t * (w + w⁻¹) + t ^ 2 * (w * w⁻¹) by ring,
    mul_inv_cancel₀ hw, show w + w⁻¹ = 2 * c by rw [← hx]; ring]
  push_cast; ring

/-- `(a²)^z = a^{2z}` for real `a > 0`. -/
theorem ofReal_sq_cpow {a : ℝ} (ha : 0 < a) (z : ℂ) :
    (((a ^ 2 : ℝ)) : ℂ) ^ z = (a : ℂ) ^ (2 * z) := by
  have ha2 : (((a ^ 2 : ℝ)) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos ha 2).ne'
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  rw [cpow_def_of_ne_zero ha2, cpow_def_of_ne_zero ha0, ← ofReal_log (pow_pos ha 2).le,
    Real.log_pow, ← ofReal_log ha.le]
  push_cast; ring_nf

/-- **Exercise 6.7-12**, scalar form: for distinct `a, b > 0` and `c ∈ [-1, 1]`,
`(a² + b² - 2abc)^{-ν} = ∑ₙ r_<ⁿ/r_>^{n+2ν} Cₙ^ν(c)`, with `r_< = min a b`, `r_> = max a b`. -/
theorem hasSum_gegenbauer_dist_real (ν : ℂ) {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (hc : |c| ≤ 1) :
    HasSum (fun n : ℕ => (gegenbauer ν n).eval (c : ℂ) * ((min a b / max a b : ℝ) : ℂ) ^ n *
        ((max a b : ℝ) : ℂ) ^ (-2 * ν))
      (((a ^ 2 + b ^ 2 - 2 * a * b * c : ℝ) : ℂ) ^ (-ν)) := by
  set R := max a b
  set t := min a b / R
  have hR : 0 < R := lt_max_of_lt_left ha
  have ht0 : 0 ≤ t := div_nonneg (le_min ha.le hb.le) hR.le
  have ht1 : t < 1 := by
    rw [div_lt_one hR]
    rcases lt_or_gt_of_ne hab with h | h
    · simp only [R, min_eq_left h.le, max_eq_right h.le]; exact h
    · simp only [R, min_eq_right h.le, max_eq_left h.le]; exact h
  have h := (hasSum_gegenbauer_real ν hc ht0 ht1).mul_right ((R : ℂ) ^ (-2 * ν))
  have hQ : 0 < 1 - 2 * c * t + t ^ 2 := by
    have := abs_le.mp hc
    nlinarith [sq_nonneg (t - c), sq_nonneg t]
  have hsplit : a ^ 2 + b ^ 2 - 2 * a * b * c = R ^ 2 * (1 - 2 * c * t + t ^ 2) := by
    have hmm : min a b * max a b = a * b := min_mul_max a b
    have hss : min a b ^ 2 + max a b ^ 2 = a ^ 2 + b ^ 2 := by
      rcases le_total a b with h | h
      · rw [min_eq_left h, max_eq_right h]
      · rw [min_eq_right h, max_eq_left h]; ring
    have hexp : R ^ 2 * (1 - 2 * c * t + t ^ 2) = R ^ 2 - 2 * c * min a b * R + min a b ^ 2 := by
      simp only [t]; field_simp
    rw [hexp]
    linear_combination (-1) * hss + 2 * c * hmm
  rw [hsplit, ofReal_mul, mul_cpow_ofReal_nonneg (by positivity) hQ.le, ofReal_sq_cpow hR]
  convert h using 1
  rw [show 2 * -ν = -2 * ν by ring]; ring

/-- **Exercise 6.7-12**: for vectors `r, r'` of different lengths in a real inner product space,
`|r - r'|^{-2ν} = ∑ₙ r_<ⁿ/r_>^{n+2ν} Cₙ^ν(cos θ)`, `cos θ = r·r'/(|r||r'|)`. -/
theorem hasSum_gegenbauer_dist {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (ν : ℂ) {r r' : E} (hr : r ≠ 0) (hr' : r' ≠ 0) (hne : ‖r‖ ≠ ‖r'‖) :
    HasSum (fun n : ℕ => (gegenbauer ν n).eval ((inner ℝ r r' / (‖r‖ * ‖r'‖) : ℝ) : ℂ) *
        ((min ‖r‖ ‖r'‖ / max ‖r‖ ‖r'‖ : ℝ) : ℂ) ^ n * ((max ‖r‖ ‖r'‖ : ℝ) : ℂ) ^ (-2 * ν))
      (((‖r - r'‖ : ℝ) : ℂ) ^ (-2 * ν)) := by
  have ha : 0 < ‖r‖ := norm_pos_iff.mpr hr
  have hb : 0 < ‖r'‖ := norm_pos_iff.mpr hr'
  have h := hasSum_gegenbauer_dist_real ν ha hb hne (abs_real_inner_div_norm_mul_norm_le_one r r')
  have hd : ‖r‖ ^ 2 + ‖r'‖ ^ 2 - 2 * ‖r‖ * ‖r'‖ * (inner ℝ r r' / (‖r‖ * ‖r'‖)) =
      ‖r - r'‖ ^ 2 := by
    rw [norm_sub_sq_real]; field_simp; ring
  rw [hd] at h
  have hpos : 0 < ‖r - r'‖ := norm_pos_iff.mpr fun h0 => hne (by rw [sub_eq_zero.mp h0])
  rwa [ofReal_sq_cpow hpos, show 2 * -ν = -2 * ν by ring] at h

/-- **Exercise 7.3-2**: for points with spherical coordinates `(a, θ, φ)`, `(b, θ', φ')`,
`a ≠ b`, and `cos γ = cos θ cos θ' + sin θ sin θ' cos(φ - φ')`,
`1/|r - r'| = ∑ₙ r_<ⁿ/r_>^{n+1} ∑_{m=-n}^{n} (-1)ᵐ P_n^m(cos θ) P_n^{-m}(cos θ') e^{im(φ-φ')}`,
where `|r - r'|² = a² + b² - 2ab cos γ`. -/
theorem hasSum_inv_dist_spherical {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (θ θ' φ φ' : ℝ) :
    HasSum (fun n : ℕ => ((min a b / max a b : ℝ) : ℂ) ^ n / (max a b : ℝ) *
        ∑ m ∈ Finset.Icc (-(n : ℤ)) n, (-1) ^ m * assocLegendreInt n m θ *
          assocLegendreInt n (-m) θ' * exp (m * ((φ - φ' : ℝ) : ℂ) * I))
      (((a ^ 2 + b ^ 2 - 2 * a * b * (Real.cos θ * Real.cos θ' +
        Real.sin θ * Real.sin θ' * Real.cos (φ - φ')) : ℝ) : ℂ) ^ (-(1 / 2 : ℂ))) := by
  set c : ℝ := Real.cos θ * Real.cos θ' + Real.sin θ * Real.sin θ' * Real.cos (φ - φ')
  have hc : |c| ≤ 1 := by
    have h1 := Real.sin_sq_add_cos_sq θ
    have h2 := Real.sin_sq_add_cos_sq θ'
    have hk := (sq_le_one_iff_abs_le_one (Real.cos (φ - φ'))).mpr (Real.abs_cos_le_one _)
    set k := Real.cos (φ - φ')
    have hs : Real.sin θ' ^ 2 * k ^ 2 ≤ Real.sin θ' ^ 2 :=
      mul_le_of_le_one_right (sq_nonneg _) hk
    refine (sq_le_one_iff_abs_le_one c).mp ?_
    have hcs : c ^ 2 + (Real.cos θ * (Real.sin θ' * k) - Real.sin θ * Real.cos θ') ^ 2 =
        (Real.cos θ ^ 2 + Real.sin θ ^ 2) * (Real.cos θ' ^ 2 + Real.sin θ' ^ 2 * k ^ 2) := by
      simp only [c]; ring
    nlinarith [sq_nonneg (Real.cos θ * (Real.sin θ' * k) - Real.sin θ * Real.cos θ')]
  have h := hasSum_gegenbauer_dist_real (1 / 2) ha hb hab hc
  refine h.congr_fun fun n => ?_
  have hR : 0 < max a b := lt_max_of_lt_left ha
  rw [show -2 * (1 / 2 : ℂ) = -1 by norm_num, cpow_neg_one]
  have hP := legendre_addition_exp n θ θ' ((φ - φ' : ℝ) : ℂ)
  have hcc : (c : ℂ) = cos (θ : ℂ) * cos (θ' : ℂ) + sin (θ : ℂ) * sin (θ' : ℂ) *
      cos ((φ - φ' : ℝ) : ℂ) := by
    simp only [c]; push_cast; rfl
  rw [hcc, hP, div_eq_mul_inv]
  ring

/-- **The binomial theorem for Gegenbauer polynomials** (from 6.4-1): if the circle coordinates
are related by `w = A w' + B` and `w⁻¹ = A w'⁻¹ + B`, then
`n! Cₙ^ν((w + w⁻¹)/2) = ∑ₘ (n choose m) Aᵐ B^{n-m} (2ν + m)_{n-m} m! Cₘ^ν((w' + w'⁻¹)/2)`. -/
theorem factorial_mul_eval_gegenbauer_affine (ν A B : ℂ) {w w' : ℂ} (hw : w ≠ 0)
    (hw' : w' ≠ 0) (h1 : w = A * w' + B) (h2 : w⁻¹ = A * w'⁻¹ + B) (n : ℕ) :
    (n.factorial : ℂ) * (gegenbauer ν n).eval ((w + w⁻¹) / 2) = ∑ m ∈ range (n + 1),
      (n.choose m : ℂ) * A ^ m * B ^ (n - m) * (ascPochhammer ℂ (n - m)).eval (2 * ν + m) *
        ((m.factorial : ℂ) * (gegenbauer ν m).eval ((w' + w'⁻¹) / 2)) := by
  rw [factorial_mul_eval_gegenbauer ν w hw, show carlsonRPolynomialNumerator₂ n ν ν w w⁻¹ =
    carlsonRPolynomialNumerator₂ n ν ν (A * w' + B) (A * w'⁻¹ + B) by rw [← h1, ← h2],
    carlsonRPolynomialNumerator₂_add_const]
  refine sum_congr rfl fun m _ => ?_
  rw [factorial_mul_eval_gegenbauer ν w' hw', carlsonRPolynomialNumerator₂_smul,
    show ν + ν = 2 * ν by ring]
  ring

/-- Circle-coordinate form of `cos`. -/
theorem cos_eq_exp_add_inv (x : ℂ) : cos x = (exp (x * I) + (exp (x * I))⁻¹) / 2 := by
  rw [Complex.cos, ← exp_neg, show -x * I = -(x * I) by ring]

/-- Circle-coordinate form of `sin`. -/
theorem sin_eq_exp_sub_inv (x : ℂ) : sin x = (exp (x * I) - (exp (x * I))⁻¹) / (2 * I) := by
  rw [Complex.sin, ← exp_neg, show -x * I = -(x * I) by ring]
  field_simp; rw [I_sq]; ring

/-- **Exercise 6.7-9** (Rainville–Carlitz), division-free form: if `sin φ ≠ 0`,
`Cₙ^ν(cos θ) = ∑ₘ (2ν + m)_{n-m}/(n - m)! (sin θ/sin φ)ᵐ (sin(φ - θ)/sin φ)^{n-m} Cₘ^ν(cos φ)`;
Carlson's form follows from `(2ν)ₙ/(2ν)ₘ = (2ν + m)_{n-m}`. -/
theorem eval_gegenbauer_cos_rainville (ν θ φ : ℂ) (hφ : sin φ ≠ 0) (n : ℕ) :
    (gegenbauer ν n).eval (cos θ) = ∑ m ∈ range (n + 1),
      (ascPochhammer ℂ (n - m)).eval (2 * ν + m) / (n - m).factorial *
        (sin θ / sin φ) ^ m * (sin (φ - θ) / sin φ) ^ (n - m) * (gegenbauer ν m).eval (cos φ) := by
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  have hA : sin θ / sin φ = (exp (θ * I) - (exp (θ * I))⁻¹) / (exp (φ * I) - (exp (φ * I))⁻¹) := by
    rw [sin_eq_exp_sub_inv θ, sin_eq_exp_sub_inv φ, div_div_div_cancel_right₀ hI]
  have hB : sin (φ - θ) / sin φ = (exp (φ * I) * (exp (θ * I))⁻¹ -
      (exp (φ * I) * (exp (θ * I))⁻¹)⁻¹) / (exp (φ * I) - (exp (φ * I))⁻¹) := by
    rw [sin_eq_exp_sub_inv (φ - θ), sin_eq_exp_sub_inv φ, div_div_div_cancel_right₀ hI, sub_mul,
      exp_sub, div_eq_mul_inv (exp (φ * I))]
  have hsφ : exp (φ * I) - (exp (φ * I))⁻¹ ≠ 0 := by
    intro h0; apply hφ; rw [sin_eq_exp_sub_inv, h0, zero_div]
  have hu := exp_ne_zero (θ * I)
  have hv := exp_ne_zero (φ * I)
  rw [cos_eq_exp_add_inv θ, cos_eq_exp_add_inv φ, hA, hB]
  generalize exp (θ * I) = u at hu hsφ ⊢
  generalize exp (φ * I) = v at hv hsφ ⊢
  have hsφ' : v ^ 2 - 1 ≠ 0 := by
    intro h0; apply hsφ; field_simp; linear_combination h0
  have h1 : u = (u - u⁻¹) / (v - v⁻¹) * v + (v * u⁻¹ - (v * u⁻¹)⁻¹) / (v - v⁻¹) := by
    field_simp; ring
  have h2 : u⁻¹ = (u - u⁻¹) / (v - v⁻¹) * v⁻¹ + (v * u⁻¹ - (v * u⁻¹)⁻¹) / (v - v⁻¹) := by
    field_simp; ring
  have h := factorial_mul_eval_gegenbauer_affine ν _ _ hu hv h1 h2 n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [← mul_right_inj' hf, h, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  rw [Nat.cast_choose ℂ hmn]
  have h1' : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have h2' : ((n - m).factorial : ℂ) ≠ 0 := by exact_mod_cast (n - m).factorial_ne_zero
  field_simp

/-- **Exercise 6.7-10**, first identity: `Pₙ(cos θ) = (2 cos θ)⁻ⁿ ∑ₘ (n choose m) Pₘ(cos 2θ)` for
`cos θ ≠ 0`. -/
theorem eval_legendre_cos_eq_sum (θ : ℂ) (hθ : cos θ ≠ 0) (n : ℕ) :
    (gegenbauer (1 / 2 : ℂ) n).eval (cos θ) = (2 * cos θ)⁻¹ ^ n *
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (gegenbauer (1 / 2 : ℂ) m).eval (cos (2 * θ)) := by
  have hw := exp_ne_zero (θ * I)
  have hc2 : cos (2 * θ) = (exp (θ * I) ^ 2 + (exp (θ * I) ^ 2)⁻¹) / 2 := by
    rw [cos_eq_exp_add_inv, show 2 * θ * I = ((2 : ℕ) : ℂ) * (θ * I) by push_cast; ring,
      exp_nat_mul]
  rw [hc2, cos_eq_exp_add_inv θ] at *
  generalize exp (θ * I) = w at hw hθ ⊢
  have hw2 : w ^ 2 ≠ 0 := pow_ne_zero 2 hw
  have hq : 1 + w ^ 2 ≠ 0 := by
    intro h0; apply hθ; field_simp; linear_combination h0
  have hq' : w ^ 2 + 1 ≠ 0 := by rwa [add_comm]
  set A := (2 * ((w + w⁻¹) / 2))⁻¹
  have h1 : w = A * w ^ 2 + A := by
    simp only [A]; field_simp
  have h2 : w⁻¹ = A * (w ^ 2)⁻¹ + A := by
    simp only [A]; field_simp; ring
  have h := factorial_mul_eval_gegenbauer_affine (1 / 2) A A hw hw2 h1 h2 n
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [← mul_right_inj' hf, h, mul_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hpoch : (ascPochhammer ℂ (n - m)).eval (2 * (1 / 2 : ℂ) + m) * (m.factorial : ℂ) =
      (n.factorial : ℂ) := by
    rw [show 2 * (1 / 2 : ℂ) + m = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
      ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial]
    have := Nat.factorial_mul_ascFactorial m (n - m)
    rw [Nat.add_sub_cancel' hmn] at this
    rw [mul_comm]; exact_mod_cast this
  have hAn : A ^ n = A ^ m * A ^ (n - m) := by rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hAn]
  linear_combination (n.choose m : ℂ) * A ^ m * A ^ (n - m) *
    (gegenbauer (1 / 2 : ℂ) m).eval ((w ^ 2 + (w ^ 2)⁻¹) / 2) * hpoch

/-- The Legendre identity of Exercise 6.7-10 (second) away from the zeros of `sin θ`. -/
theorem sin_pow_mul_eval_legendre_sin_of_ne (θ : ℂ) (hθ : sin θ ≠ 0) (n : ℕ) :
    sin θ ^ n * (gegenbauer (1 / 2 : ℂ) n).eval (sin θ) =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (-cos θ) ^ m *
        (gegenbauer (1 / 2 : ℂ) m).eval (cos θ) := by
  set u := exp (θ * I)
  have hu : u ≠ 0 := exp_ne_zero _
  have hw : -I * u ≠ 0 := mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hu
  have hc : cos θ = (u + u⁻¹) / 2 := cos_eq_exp_add_inv θ
  have hs : sin θ = (-I * u + (-I * u)⁻¹) / 2 := by
    rw [sin_eq_exp_sub_inv]; field_simp; ring_nf; rw [I_sq]; ring
  set A := -cos θ / sin θ
  set B := 1 / sin θ
  have hsin : sin θ = (u - u⁻¹) / (2 * I) := sin_eq_exp_sub_inv θ
  have hu2 : u - u⁻¹ ≠ 0 := by
    intro h; apply hθ; rw [hsin, h, zero_div]
  have hu3 : -1 + u ^ 2 ≠ 0 := by
    intro h; apply hu2; field_simp; linear_combination h
  have hu4 : u ^ 2 - 1 ≠ 0 := by
    intro h; apply hu3; linear_combination h
  have h1 : -I * u = A * u + B := by
    simp only [A, B]; rw [hc, hsin]; field_simp; ring_nf
  have h2 : (-I * u)⁻¹ = A * u⁻¹ + B := by
    simp only [A, B]; rw [hc, hsin]; field_simp; ring_nf; rw [I_sq]; ring
  have h := factorial_mul_eval_gegenbauer_affine (1 / 2) A B hw hu h1 h2 n
  rw [← hs, ← hc] at h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [← mul_right_inj' hf, mul_left_comm, h, mul_sum, mul_sum]
  refine sum_congr rfl fun m hm => ?_
  have hmn : m ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hm)
  have hpoch : (ascPochhammer ℂ (n - m)).eval (2 * (1 / 2 : ℂ) + m) * (m.factorial : ℂ) =
      (n.factorial : ℂ) := by
    rw [show 2 * (1 / 2 : ℂ) + m = ((m + 1 : ℕ) : ℂ) by push_cast; ring,
      ← ascPochhammer_eval_cast, ascPochhammer_nat_eq_ascFactorial]
    have := Nat.factorial_mul_ascFactorial m (n - m)
    rw [Nat.add_sub_cancel' hmn] at this
    rw [mul_comm]; exact_mod_cast this
  have hsn : sin θ ^ n = sin θ ^ m * sin θ ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  have hA : sin θ ^ m * A ^ m = (-cos θ) ^ m := by
    rw [← mul_pow]; simp only [A]; field_simp
  have hB : sin θ ^ (n - m) * B ^ (n - m) = 1 := by
    rw [← mul_pow]; simp only [B]; field_simp; simp
  rw [hsn, ← hpoch]
  linear_combination (n.choose m : ℂ) * (ascPochhammer ℂ (n - m)).eval (2 * (1 / 2 : ℂ) + m) *
    (m.factorial : ℂ) * (gegenbauer (1 / 2 : ℂ) m).eval (cos θ) *
    ((sin θ ^ (n - m) * B ^ (n - m)) * hA + (-cos θ) ^ m * hB)

/-- **Exercise 6.7-10**, second identity:
`(sin θ)ⁿ Pₙ(sin θ) = ∑ₘ (n choose m) (-cos θ)ᵐ Pₘ(cos θ)`. -/
theorem sin_pow_mul_eval_legendre_sin (θ : ℂ) (n : ℕ) :
    sin θ ^ n * (gegenbauer (1 / 2 : ℂ) n).eval (sin θ) =
      ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (-cos θ) ^ m *
        (gegenbauer (1 / 2 : ℂ) m).eval (cos θ) := by
  have hL : Continuous fun θ : ℂ => sin θ ^ n * (gegenbauer (1 / 2 : ℂ) n).eval (sin θ) := by
    fun_prop
  have hR : Continuous fun θ : ℂ => ∑ m ∈ range (n + 1), (n.choose m : ℂ) * (-cos θ) ^ m *
      (gegenbauer (1 / 2 : ℂ) m).eval (cos θ) := by fun_prop
  have hbad : {θ : ℂ | sin θ = 0}.Countable := by
    refine (Set.countable_range fun k : ℤ => (k : ℂ) * Real.pi).mono fun θ hθ => ?_
    obtain ⟨k, hk⟩ := sin_eq_zero_iff.mp hθ
    exact ⟨k, hk.symm⟩
  have h := hL.ext_on (hbad.dense_compl ℂ) hR fun θ hθ => sin_pow_mul_eval_legendre_sin_of_ne θ hθ n
  exact congrFun h θ

/-- `(1/2)ₖ 4ᵏ k! = (2k)!`. -/
theorem ascPochhammer_half_mul (k : ℕ) :
    (ascPochhammer ℂ k).eval (1 / 2 : ℂ) * 4 ^ k * k.factorial = (2 * k).factorial := by
  have h := ascPochhammer_eval_double (1 / 2 : ℂ) k
  rw [show 2 * (1 / 2 : ℂ) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    ascPochhammer_eval_one, ascPochhammer_eval_one] at h
  rw [h]; ring

/-- `(3/2)ₖ 4ᵏ k! = (2k + 1)!`. -/
theorem ascPochhammer_three_halves_mul (k : ℕ) :
    (ascPochhammer ℂ k).eval (3 / 2 : ℂ) * 4 ^ k * k.factorial = (2 * k + 1).factorial := by
  have h := ascPochhammer_eval_double (1 : ℂ) k
  rw [show (1 : ℂ) + 1 / 2 = 3 / 2 by norm_num, ascPochhammer_eval_one] at h
  have h2 : (ascPochhammer ℂ (2 * k)).eval (2 * 1 : ℂ) = (2 * k + 1).factorial := by
    have := ascPochhammer_eval_one ℂ (2 * k + 1)
    rw [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_X, eval_one,
      one_mul] at this
    rw [show (2 * 1 : ℂ) = 1 + 1 by norm_num, this]
  rw [h2] at h
  rw [h]; ring

/-- **Exercise 6.9-9** (even degree):
`C₂ₙ^ν(x) = (-1)ⁿ (ν)ₙ/n! ₂F₁(-n, ν + n; 1/2; x²)`. -/
theorem eval_gegenbauer_two_mul_eq_hypergeometric (ν x : ℂ) (n : ℕ) :
    (gegenbauer ν (2 * n)).eval x = (-1) ^ n * (ascPochhammer ℂ n).eval ν / n.factorial *
      ordinaryHypergeometric (-(n : ℂ)) (ν + n) (1 / 2) (x ^ 2) := by
  rw [eval_gegenbauer_eq_sum, ordinaryHypergeometric_neg_natCast, Finset.mul_sum,
    show 2 * n + 1 = (n + 1) + n by ring, Finset.sum_range_add]
  rw [Finset.sum_eq_zero (s := range n) fun j hj => by
    rw [Nat.choose_eq_zero_of_lt (by simp at hj; omega)]; simp, add_zero,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [show k + j + 1 - 1 - k = j by omega, show 2 * (k + j) - j = 2 * k + j by omega,
    show 2 * (k + j) - 2 * j = 2 * k by omega]
  have hc1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * k + j by omega)
  rw [show 2 * k + j - j = 2 * k by omega] at hc1
  have hc2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + j by omega)
  rw [show k + j - k = j by omega] at hc2
  have hp := ascPochhammer_add_eval ν (k + j) k
  rw [show k + j + k = 2 * k + j by ring] at hp
  have hh := ascPochhammer_half_mul k
  have hh0 : (ascPochhammer ℂ k).eval (1 / 2 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) k
  rw [ascPochhammer_eval_neg_natCast, ← (by exact_mod_cast hc1 :
    ((2 * k + j).choose j : ℂ) * j.factorial * (2 * k).factorial = (2 * k + j).factorial),
    ← (by exact_mod_cast hc2 :
    ((k + j).choose k : ℂ) * k.factorial * j.factorial = (k + j).factorial), hp, ← hh]
  push_cast
  have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h2 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h3 : ((2 * k + j).choose j : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h4 : ((k + j).choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [mul_pow (2 : ℂ) x (2 * k), pow_mul (2 : ℂ) 2 k, pow_mul x 2 k, pow_add (-1 : ℂ) k j]
  norm_num
  rcases neg_one_pow_eq_or ℂ k with hs | hs <;> rw [hs] <;> field_simp

/-- **Exercise 6.9-9** (odd degree):
`C₂ₙ₊₁^ν(x) = (-1)ⁿ (ν)ₙ₊₁/n! 2x ₂F₁(-n, ν + n + 1; 3/2; x²)`. -/
theorem eval_gegenbauer_two_mul_add_one_eq_hypergeometric (ν x : ℂ) (n : ℕ) :
    (gegenbauer ν (2 * n + 1)).eval x =
      (-1) ^ n * (ascPochhammer ℂ (n + 1)).eval ν / n.factorial * (2 * x) *
        ordinaryHypergeometric (-(n : ℂ)) (ν + n + 1) (3 / 2) (x ^ 2) := by
  rw [eval_gegenbauer_eq_sum, ordinaryHypergeometric_neg_natCast, Finset.mul_sum,
    show 2 * n + 1 + 1 = (n + 1) + (n + 1) by ring, Finset.sum_range_add]
  rw [add_eq_left.mpr (Finset.sum_eq_zero (s := range (n + 1)) (f := fun j : ℕ =>
      (ascPochhammer ℂ (2 * n + 1 - (n + 1 + j))).eval ν /
        ((2 * n + 1 - (n + 1 + j)).factorial : ℂ) *
        ((2 * n + 1 - (n + 1 + j)).choose (n + 1 + j) : ℂ) * (-1) ^ (n + 1 + j) *
        (2 * x) ^ (2 * n + 1 - 2 * (n + 1 + j))) fun j _ => by
    rw [Nat.choose_eq_zero_of_lt (by omega)]; simp), ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  obtain ⟨j, rfl⟩ : ∃ j, n = k + j := ⟨n - k, by omega⟩
  rw [show k + j + 1 - 1 - k = j by omega, show 2 * (k + j) + 1 - j = 2 * k + j + 1 by omega,
    show 2 * (k + j) + 1 - 2 * j = 2 * k + 1 by omega]
  have hc1 := Nat.choose_mul_factorial_mul_factorial (show j ≤ 2 * k + j + 1 by omega)
  rw [show 2 * k + j + 1 - j = 2 * k + 1 by omega] at hc1
  have hc2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + j by omega)
  rw [show k + j - k = j by omega] at hc2
  have hp := ascPochhammer_add_eval ν (k + j + 1) k
  rw [show k + j + 1 + k = 2 * k + j + 1 by ring] at hp
  have hh := ascPochhammer_three_halves_mul k
  have hh0 : (ascPochhammer ℂ k).eval (3 / 2 : ℂ) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) k
  rw [ascPochhammer_eval_neg_natCast, ← (by exact_mod_cast hc1 :
    ((2 * k + j + 1).choose j : ℂ) * j.factorial * (2 * k + 1).factorial =
      (2 * k + j + 1).factorial),
    ← (by exact_mod_cast hc2 :
    ((k + j).choose k : ℂ) * k.factorial * j.factorial = (k + j).factorial), hp, ← hh]
  push_cast
  have h1 : (j.factorial : ℂ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
  have h2 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h3 : ((2 * k + j + 1).choose j : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have h4 : ((k + j).choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  rw [mul_pow (2 : ℂ) x (2 * k + 1), pow_succ (2 : ℂ), pow_mul (2 : ℂ) 2 k, pow_succ x,
    pow_mul x 2 k, pow_add (-1 : ℂ) k j]
  norm_num
  rcases neg_one_pow_eq_or ℂ k with hs | hs <;> rw [hs] <;> field_simp <;> ring_nf

/-- `sin (x + nπ) = (-1)ⁿ sin x` for complex `x`. -/
theorem sin_add_nat_mul_pi_complex (x : ℂ) (n : ℕ) :
    sin (x + n * Real.pi) = (-1) ^ n * sin x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, sin_add_pi, ih, pow_succ]; ring

/-- `Uₘ(cos θ) sin θ = sin((m + 1)θ)` with `Uₘ = Cₘ¹`. -/
theorem eval_gegenbauer_one_cos_mul_sin (θ : ℂ) (m : ℕ) :
    (gegenbauer (1 : ℂ) m).eval (cos θ) * sin θ = sin ((m + 1) * θ) := by
  rw [gegenbauer_one_param_eq_chebyshev_U]
  have := Chebyshev.U_complex_cos θ m
  push_cast at this
  exact this

/-- **Exercise 6.9-11** (odd multiple, `cos²` form):
`sin (2n + 1)θ = (-1)ⁿ sin θ ₂F₁(-n, 1 + n; 1/2; cos² θ)`. -/
theorem sin_two_mul_add_one_mul_eq_hypergeometric_cos (θ : ℂ) (n : ℕ) :
    sin ((2 * n + 1) * θ) =
      (-1) ^ n * sin θ * ordinaryHypergeometric (-(n : ℂ)) (1 + n) (1 / 2) (cos θ ^ 2) := by
  have h := eval_gegenbauer_one_cos_mul_sin θ (2 * n)
  rw [eval_gegenbauer_two_mul_eq_hypergeometric, ascPochhammer_eval_one] at h
  push_cast at h
  rw [← h]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.9-11** (even multiple, `cos²` form):
`sin 2(n + 1)θ = (-1)ⁿ (n + 1) sin 2θ ₂F₁(-n, n + 2; 3/2; cos² θ)`. Carlson writes the degree
as `n ≥ 1` with first parameter `1 - n`. -/
theorem sin_two_mul_succ_mul_eq_hypergeometric_cos (θ : ℂ) (n : ℕ) :
    sin (2 * (n + 1) * θ) = (-1) ^ n * (n + 1) * sin (2 * θ) *
      ordinaryHypergeometric (-(n : ℂ)) (n + 2) (3 / 2) (cos θ ^ 2) := by
  have h := eval_gegenbauer_one_cos_mul_sin θ (2 * n + 1)
  rw [eval_gegenbauer_two_mul_add_one_eq_hypergeometric, ascPochhammer_eval_one,
    Nat.factorial_succ] at h
  push_cast at h
  rw [show 2 * ((n : ℂ) + 1) * θ = (2 * n + 1 + 1) * θ by ring, ← h, sin_two_mul,
    show (1 : ℂ) + n + 1 = n + 2 by ring]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.9-10** (odd multiple, `sin²` form):
`cos (2n + 1)θ = cos θ ₂F₁(-n, n + 1; 1/2; sin² θ)`. -/
theorem cos_two_mul_add_one_mul_eq_hypergeometric_sin (θ : ℂ) (n : ℕ) :
    cos ((2 * n + 1) * θ) =
      cos θ * ordinaryHypergeometric (-(n : ℂ)) (n + 1) (1 / 2) (sin θ ^ 2) := by
  have h := sin_two_mul_add_one_mul_eq_hypergeometric_cos (Real.pi / 2 - θ) n
  rw [sin_pi_div_two_sub, cos_pi_div_two_sub,
    show (2 * (n : ℂ) + 1) * (Real.pi / 2 - θ) = Real.pi / 2 - (2 * n + 1) * θ + n * Real.pi by
      ring, sin_add_nat_mul_pi_complex, sin_pi_div_two_sub, add_comm (1 : ℂ)] at h
  have h1 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h1 (by rw [h]; ring)

/-- **Exercise 6.9-11** (even multiple, `sin²` form):
`sin 2(n + 1)θ = (n + 1) sin 2θ ₂F₁(-n, n + 2; 3/2; sin² θ)`. -/
theorem sin_two_mul_succ_mul_eq_hypergeometric_sin (θ : ℂ) (n : ℕ) :
    sin (2 * (n + 1) * θ) =
      (n + 1) * sin (2 * θ) * ordinaryHypergeometric (-(n : ℂ)) (n + 2) (3 / 2) (sin θ ^ 2) := by
  have h := sin_two_mul_succ_mul_eq_hypergeometric_cos (Real.pi / 2 - θ) n
  rw [cos_pi_div_two_sub,
    show 2 * ((n : ℂ) + 1) * (Real.pi / 2 - θ) = -(2 * (n + 1) * θ) + ((n + 1 : ℕ) : ℂ) * Real.pi
      by push_cast; ring, sin_add_nat_mul_pi_complex, sin_neg,
    show 2 * (Real.pi / 2 - θ) = -(2 * θ) + ((1 : ℕ) : ℂ) * Real.pi by push_cast; ring,
    sin_add_nat_mul_pi_complex, sin_neg] at h
  have h1 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  refine mul_left_cancel₀ h1 ?_
  linear_combination h

/-- **Exercise 6.10-10**: if `(ν + 1/2)ₙ ≠ 0`, then
`Cₙ^ν(x) = (2ν)ₙ/n! ₂F₁(-n, 2ν + n; ν + 1/2; (1 - x)/2)`. -/
theorem eval_gegenbauer_eq_hypergeometric (ν x : ℂ) (n : ℕ)
    (hν : (ascPochhammer ℂ n).eval (ν + 1 / 2) ≠ 0) :
    (gegenbauer ν n).eval x = (ascPochhammer ℂ n).eval (2 * ν) / n.factorial *
      ordinaryHypergeometric (-(n : ℂ)) (2 * ν + n) (ν + 1 / 2) ((1 - x) / 2) := by
  rw [gegenbauer, eval_comp, shiftedGegenbauer, eval_finsetSum, ordinaryHypergeometric_neg_natCast,
    mul_sum, ← Finset.Nat.sum_antidiagonal_swap, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simp at hk; omega
  obtain ⟨i, rfl⟩ : ∃ i, n = k + i := ⟨n - k, by omega⟩
  simp only [Prod.swap_prod_mk, show k + i - k = i by omega]
  have hνk : (ascPochhammer ℂ k).eval (ν + 1 / 2) ≠ 0 := by
    have h := ascPochhammer_add_eval (ν + 1 / 2) k i
    intro h0; apply hν; rw [h, h0, zero_mul]
  have hp1 := ascPochhammer_add_eval (2 * ν) (k + i) k
  have hp2 := ascPochhammer_add_eval (2 * ν) (2 * k) i
  have hd := ascPochhammer_eval_double ν k
  rw [show k + i + k = 2 * k + i by ring] at hp1
  rw [hp2, hd] at hp1
  have hc := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + i by omega)
  rw [show k + i - k = i by omega] at hc
  rw [ascPochhammer_eval_neg_natCast, ← (by exact_mod_cast hc :
    ((k + i).choose k : ℂ) * k.factorial * i.factorial = (k + i).factorial)]
  simp only [eval_mul, eval_C, eval_pow, eval_X, eval_sub, eval_one]
  norm_num only [map_div₀, map_pow, map_neg, map_ofNat, map_one, map_mul, map_natCast]
  push_cast
  have h1 : (i.factorial : ℂ) ≠ 0 := by exact_mod_cast i.factorial_ne_zero
  have h2 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast k.factorial_ne_zero
  have h4 : ((k + i).choose k : ℂ) ≠ 0 := by exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hpow : (-4 : ℂ) ^ k = (-1) ^ k * 4 ^ k := by rw [← mul_pow]; norm_num
  rw [hpow]
  push_cast at hp1
  rw [show 2 * ν + 2 * (k : ℂ) = 2 * ν + 2 * k from rfl]
  generalize (ascPochhammer ℂ k).eval (ν + 1 / 2) = P at hνk hp1 ⊢
  generalize (ascPochhammer ℂ (k + i)).eval (2 * ν) = Q at hp1 ⊢
  generalize (ascPochhammer ℂ k).eval (2 * ν + (k + i)) = R at hp1 ⊢
  generalize (ascPochhammer ℂ i).eval (2 * ν + 2 * k) = S at hp1 ⊢
  generalize (ascPochhammer ℂ k).eval ν = V at hp1 ⊢
  field_simp
  linear_combination (1 / 2 + x * (-1 / 2)) ^ k * hp1

/-- **Exercise 6.10-11**: for `sin θ ≠ 0`,
`2ⁿ Rₙ(-1/2 - n, -1/2 - n; cos θ + 1, cos θ - 1) = sin (n + 1)θ / sin θ`, with
`Rₙ = Nₙ/(-1 - 2n)ₙ`. -/
theorem two_pow_mul_carlsonRPolynomial_cos (n : ℕ) {θ : ℂ} (hθ : sin θ ≠ 0) :
    2 ^ n * (carlsonRPolynomialNumerator₂ n (-(1 / 2) - n) (-(1 / 2) - n) (cos θ + 1)
      (cos θ - 1) / (ascPochhammer ℂ n).eval (-(1 / 2) - 1 / 2 - 2 * (n : ℂ))) =
        sin ((n + 1) * θ) / sin θ := by
  have hs2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hsin : sin θ = 2 * sin (θ / 2) * cos (θ / 2) := by
    rw [← sin_two_mul]; ring_nf
  have hc2 : cos θ = 2 * cos (θ / 2) ^ 2 - 1 := by
    rw [← cos_two_mul]; ring_nf
  have hcos : cos (θ / 2) ≠ 0 := by intro h; apply hθ; rw [hsin, h, mul_zero]
  have hsin2 : sin (θ / 2) ≠ 0 := by intro h; apply hθ; rw [hsin, h, mul_zero, zero_mul]
  have hr : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h; rw [h] at hs2; norm_num at hs2
  set a := ((Real.sqrt 2 : ℝ) : ℂ) * cos (θ / 2)
  set b := I * ((Real.sqrt 2 : ℝ) : ℂ) * sin (θ / 2)
  have ha : a ≠ 0 := mul_ne_zero hr hcos
  have hb : b ≠ 0 := mul_ne_zero (mul_ne_zero I_ne_zero hr) hsin2
  have ha2 : a ^ 2 = cos θ + 1 := by
    simp only [a]; rw [mul_pow, hs2, hc2]; ring
  have hb2 : b ^ 2 = cos θ - 1 := by
    simp only [b]; rw [mul_pow, mul_pow, hs2, I_sq, hc2]
    linear_combination (-2) * sin_sq_add_cos_sq (θ / 2)
  have h := carlsonRPolynomial_chebyshevU n ha hb
  rw [ha2, hb2] at h
  rw [h]
  have hpl : (a + b) / 2 = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * exp (θ / 2 * I) := by
    rw [exp_mul_I]; simp only [a, b]; ring
  have hmi : (a - b) / 2 = ((Real.sqrt 2 : ℝ) : ℂ) / 2 * exp (-(θ / 2) * I) := by
    rw [exp_mul_I, cos_neg, sin_neg]; simp only [a, b]; ring
  have hq : (((Real.sqrt 2 : ℝ) : ℂ) / 2) ^ (2 * n + 2) = (1 / 2) ^ (n + 1) := by
    rw [show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, div_pow, hs2]; norm_num
  have hE (z : ℂ) : exp (z / 2 * I) ^ (2 * n + 2) = exp ((n + 1) * z * I) := by
    rw [← exp_nat_mul]; push_cast; ring_nf
  have hab : a * b = I * sin θ := by
    simp only [a, b]
    rw [hsin]
    linear_combination (cos (θ / 2) * I * sin (θ / 2)) * hs2
  rw [hpl, hmi, mul_pow, mul_pow, hq, hE, show -(θ / 2) = -θ / 2 by ring, hE, hab]
  have h2s := two_sin ((n + 1) * θ)
  have hpow : (2 : ℂ) ^ n * (1 / 2) ^ (n + 1) = 1 / 2 := by
    rw [pow_succ, ← mul_assoc, ← mul_pow]; norm_num
  field_simp
  rw [hpow]
  rw [neg_mul] at h2s
  linear_combination (-I / 2) * h2s +
    ((exp ((n + 1) * θ * I) - exp (-((n + 1) * θ * I))) / 2) * I_sq

/-- The Pochhammer identity `4ⁿ (1/2 + α)ₙ (-α - n)ₙ = (1 + 2α)ₙ (-2α - 2n)ₙ`. -/
theorem four_pow_mul_ascPochhammer_half_add (α : ℂ) (n : ℕ) :
    4 ^ n * (ascPochhammer ℂ n).eval (1 / 2 + α) * (ascPochhammer ℂ n).eval (-α - n) =
      (ascPochhammer ℂ n).eval (1 + 2 * α) * (ascPochhammer ℂ n).eval (-2 * α - 2 * n) := by
  have h1 := ascPochhammer_one_sub_sub (α + 1) n
  have h2 := ascPochhammer_one_sub_sub (2 * α + n + 1) n
  rw [show 1 - (α + 1) - (n : ℂ) = -α - n by ring] at h1
  rw [show 1 - (2 * α + n + 1) - (n : ℂ) = -2 * α - 2 * n by ring] at h2
  have hd := ascPochhammer_eval_double (1 / 2 + α) n
  rw [show 2 * (1 / 2 + α) = 1 + 2 * α by ring, show 1 / 2 + α + 1 / 2 = α + 1 by ring,
    show (2 * n : ℕ) = n + n from two_mul n, ascPochhammer_add_eval,
    show 1 + 2 * α + n = 2 * α + n + 1 by ring] at hd
  rw [h1, h2]
  linear_combination -(-1) ^ n * hd

/-- **Exercise 6.10-8** in division-free numerator form:
`4ⁿ (1/2 + α)ₙ Nₙ(-α - n, -α - n; x², y²) =
(-2α - 2n)ₙ Nₙ(1/2 + α, 1/2 + α; (x + y)², (x - y)²)`. Dividing by `(-2α - 2n)ₙ (1 + 2α)ₙ` gives
Carlson's `(1/2 + α)ₙ Rₙ(-α - n, -α - n; x², y²) =
2^{-2n} (1 + 2α)ₙ Rₙ(1/2 + α, 1/2 + α; (x + y)², (x - y)²)`. -/
theorem carlsonRPolynomialNumerator₂_neg_sub_sq (α x y : ℂ) (n : ℕ) :
    4 ^ n * (ascPochhammer ℂ n).eval (1 / 2 + α) *
        carlsonRPolynomialNumerator₂ n (-α - n) (-α - n) (x ^ 2) (y ^ 2) =
      (ascPochhammer ℂ n).eval (-2 * α - 2 * n) *
        carlsonRPolynomialNumerator₂ n (1 / 2 + α) (1 / 2 + α) ((x + y) ^ 2) ((x - y) ^ 2) := by
  have hL : Continuous fun α : ℂ => 4 ^ n * (ascPochhammer ℂ n).eval (1 / 2 + α) *
      carlsonRPolynomialNumerator₂ n (-α - n) (-α - n) (x ^ 2) (y ^ 2) := by
    unfold carlsonRPolynomialNumerator₂; fun_prop
  have hR : Continuous fun α : ℂ => (ascPochhammer ℂ n).eval (-2 * α - 2 * n) *
      carlsonRPolynomialNumerator₂ n (1 / 2 + α) (1 / 2 + α) ((x + y) ^ 2) ((x - y) ^ 2) := by
    unfold carlsonRPolynomialNumerator₂; fun_prop
  have hbad : {α : ℂ | (ascPochhammer ℂ n).eval (-α - n) = 0}.Countable := by
    refine (Set.countable_range fun k : ℕ => (k : ℂ) - n).mono fun α hα => ?_
    obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 hα
    exact ⟨k, by simp only; linear_combination hk⟩
  have h := hL.ext_on (hbad.dense_compl ℂ) hR fun α hα => by
    have hα' : (ascPochhammer ℂ n).eval (-α - n) ≠ 0 := hα
    have hq := carlsonRPolynomialNumerator₂_secondQuadratic n (-α - n) x y
    rw [show 1 - 2 * (-α - (n : ℂ)) - 2 * n = 1 + 2 * α by ring,
      show 1 / 2 - (-α - (n : ℂ)) - n = 1 / 2 + α by ring] at hq
    have hK := four_pow_mul_ascPochhammer_half_add α n
    refine mul_left_cancel₀ hα' ?_
    linear_combination carlsonRPolynomialNumerator₂ n (-α - n) (-α - n) (x ^ 2) (y ^ 2) * hK +
      (ascPochhammer ℂ n).eval (-2 * α - 2 * n) * hq
  exact congrFun h α

/-- `(w²)^s = w^{2s}` for `re w > 0`. -/
theorem sq_cpow_of_re_pos {w : ℂ} (hw : 0 < w.re) (s : ℂ) : (w ^ 2) ^ s = w ^ (2 * s) := by
  have ha : |w.arg| < Real.pi / 2 := abs_arg_lt_pi_div_two_iff.mpr (Or.inl hw)
  have him : (log w * 2).im = 2 * w.arg := by simp [log_im]; ring
  rw [cpow_mul (y := 2) s (by rw [him]; linarith [abs_lt.mp ha])
    (by rw [him]; linarith [abs_lt.mp ha]), show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num,
    cpow_natCast]

/-- **Exercise 6.10-12**, first formula, regularized: for `re x, re y > 0`,
`R_{1/2-β}(β, β; x², y²)/Γ(2β) = q(β) ((x + y)/2)^{1-2β}/Γ(β + 1/2)`, where
`q(β) = Γ(β + 1/2)/Γ(2β)` is `quadraticGammaRatio β`. With `re β > 0` this is Carlson's
`R_{1/2-β}(β, β; x², y²) = ((x + y)/2)^{1-2β}` (`carlsonR_one_half_sub_pair_sq`). -/
theorem regCarlsonR_one_half_sub_pair_sq (β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR (1 / 2 - β) (pair β β) (pair (x ^ 2) (y ^ 2)) =
      quadraticGammaRatio β * ((x + y) / 2) ^ (1 - 2 * β) * (Gamma (β + 1 / 2))⁻¹ := by
  rw [regRSlit_secondQuadratic _ β x y hx hy, show 2 * β + (1 / 2 - β) = β + 1 / 2 by ring,
    show 1 / 2 - β - (1 / 2 - β) = (0 : ℂ) by ring,
    regCarlsonR_pair_zero_right _ _ (meanSquares_mem_slitDomain hx hy)]
  have hw : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re, add_re]; positivity
  simp only [pair, Matrix.cons_val_zero, arithmeticMeanSq]
  rw [sq_cpow_of_re_pos hw, show 2 * (1 / 2 - β) = 1 - 2 * β by ring, mul_assoc]

/-- **Exercise 6.10-12**, second formula, regularized: for `re x, re y > 0`,
`R_{-1/2-β}(β, β; x², y²)/Γ(2β) = q(β) (xy)⁻¹ ((x + y)/2)^{1-2β}/Γ(β + 1/2)`. -/
theorem regCarlsonR_neg_one_half_sub_pair_sq (β : ℂ) {x y : ℂ} (hx : 0 < x.re) (hy : 0 < y.re) :
    regCarlsonR (-(1 / 2) - β) (pair β β) (pair (x ^ 2) (y ^ 2)) =
      quadraticGammaRatio β * ((x * y)⁻¹ * ((x + y) / 2) ^ (1 - 2 * β)) *
        (Gamma (β + 1 / 2))⁻¹ := by
  rw [regRSlit_secondQuadratic _ β x y hx hy, show 2 * β + (-(1 / 2) - β) = β - 1 / 2 by ring,
    show 1 / 2 - β - (-(1 / 2) - β) = (1 : ℂ) by ring]
  have h := regCarlsonR_neg_sum_sub_nat 0 (pair (β - 1 / 2) 1)
    (meanSquares_mem_slitDomain hx hy)
  rw [sum_pair, show β - 1 / 2 + 1 = β + 1 / 2 by ring, Nat.cast_zero, sub_zero,
    regCarlsonRPolynomial_zero, Fin.prod_univ_two, sum_pair,
    show β - 1 / 2 + 1 = β + 1 / 2 by ring] at h
  rw [show -(1 / 2) - β = -(β + 1 / 2) by ring, h]
  have hw : 0 < ((x + y) / 2).re := by simp only [div_ofNat_re, add_re]; positivity
  simp only [pair, Matrix.cons_val_zero, Matrix.cons_val_one, arithmeticMeanSq, geometricMeanSq]
  rw [sq_cpow_of_re_pos hw, show 2 * -(β - 1 / 2) = 1 - 2 * β by ring, cpow_neg_one]
  ring

/-- **Exercise 6.10-12** in Carlson's normalization, for `re β > 0` and `re x, re y > 0`:
`R_{1/2-β}(β, β; x², y²) = ((x + y)/2)^{1-2β}` and
`R_{-1/2-β}(β, β; x², y²) = (xy)⁻¹ ((x + y)/2)^{1-2β}`. -/
theorem carlsonR_one_half_sub_pair_sq {β : ℂ} (hβ : 0 < β.re) {x y : ℂ} (hx : 0 < x.re)
    (hy : 0 < y.re) :
    carlsonR (1 / 2 - β) (pair β β) (pair (x ^ 2) (y ^ 2)) = ((x + y) / 2) ^ (1 - 2 * β) ∧
      carlsonR (-(1 / 2) - β) (pair β β) (pair (x ^ 2) (y ^ 2)) =
        (x * y)⁻¹ * ((x + y) / 2) ^ (1 - 2 * β) := by
  have hG := Gamma_mul_quadraticGammaRatio hβ
  have hG0 : Gamma (β + 1 / 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; linarith)
  refine ⟨?_, ?_⟩
  · rw [carlsonR, sum_pair, regCarlsonR_one_half_sub_pair_sq β hx hy, ← mul_assoc, ← mul_assoc,
      hG]
    generalize Gamma (β + 1 / 2) = G at hG0 ⊢
    field_simp
  · rw [carlsonR, sum_pair, regCarlsonR_neg_one_half_sub_pair_sq β hx hy, ← mul_assoc,
      ← mul_assoc, hG]
    generalize Gamma (β + 1 / 2) = G at hG0 ⊢
    field_simp

/-- **Exercise 6.10-7** in division-free form: if `S² = x² - 1` and `S ≠ 0`, then
`(1 - 2ν - 2n)ₙ Cₙ^ν(x) = (ν)ₙ (2S)ⁿ Cₙ^{1/2-ν-n}(x/S)`. Dividing by
`(1 - 2ν - 2n)ₙ = (-1)ⁿ (2ν)₂ₙ/(2ν)ₙ` gives Carlson's
`Cₙ^ν(x) = (-2)^{-n} (2ν)ₙ/(ν + 1/2)ₙ (x² - 1)^{n/2} Cₙ^{1/2-ν-n}(x (x² - 1)^{-1/2})`. -/
theorem ascPochhammer_mul_eval_gegenbauer_reflect (ν x S : ℂ) (n : ℕ) (hS : S ^ 2 = x ^ 2 - 1)
    (hS0 : S ≠ 0) :
    (ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) * (gegenbauer ν n).eval x =
      (ascPochhammer ℂ n).eval ν * (2 * S) ^ n *
        (gegenbauer (1 / 2 - ν - n) n).eval (x / S) := by
  set w := x + S
  have hw1 : w * (x - S) = 1 := by simp only [w]; linear_combination -hS
  have hw : w ≠ 0 := left_ne_zero_of_mul_eq_one hw1
  have hwi : w⁻¹ = x - S := by rw [inv_eq_of_mul_eq_one_right hw1]
  have hX : x = (w + w⁻¹) / 2 := by rw [hwi]; simp only [w]; ring
  have hx1 : x + 1 ≠ 0 := by
    intro h; apply hS0
    have : S ^ 2 = 0 := by rw [hS, show x = -1 by linear_combination h]; ring
    exact pow_eq_zero_iff (two_ne_zero) |>.mp this
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq w (by norm_num : 0 < 2)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp; exact hw hp.symm
  have hq := carlsonRPolynomialNumerator₂_secondQuadratic n ν p p⁻¹
  have hp2 : p ^ 2 = w := hp
  rw [hp2, inv_pow, hp2] at hq
  set z := (x + 1) / S
  have hz : z ≠ 0 := div_ne_zero hx1 hS0
  have hxw : w + w⁻¹ = 2 * x := by rw [hX]; ring
  have hplus : (p + p⁻¹) ^ 2 = 2 * S * z := by
    have e : (p + p⁻¹) ^ 2 = p ^ 2 + (p ^ 2)⁻¹ + 2 := by field_simp; ring
    rw [e, hp2, hxw]; simp only [z]; field_simp
  have hminus : (p - p⁻¹) ^ 2 = 2 * S * z⁻¹ := by
    have e : (p - p⁻¹) ^ 2 = p ^ 2 + (p ^ 2)⁻¹ - 2 := by field_simp; ring
    rw [e, hp2, hxw]; simp only [z]; field_simp; linear_combination -hS
  have hzz : (z + z⁻¹) / 2 = x / S := by
    simp only [z]; field_simp; linear_combination hS
  rw [hplus, hminus, carlsonRPolynomialNumerator₂_smul,
    ← factorial_mul_eval_gegenbauer ν w hw, ← factorial_mul_eval_gegenbauer _ z hz, ← hX,
    hzz] at hq
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  refine mul_left_cancel₀ hf ?_
  linear_combination hq

open scoped goldenRatio in
/-- **Exercise 6.10-9**, Fibonacci numbers: `F_{n+1} = Rₙ(-1/2 - n, -1/2 - n; 1 + 2i, 1 - 2i)`,
with `Rₙ = Nₙ/(-1 - 2n)ₙ`. -/
theorem carlsonRPolynomial_fib (n : ℕ) :
    carlsonRPolynomialNumerator₂ n (-(1 / 2) - n) (-(1 / 2) - n) (1 + 2 * I) (1 - 2 * I) /
      (ascPochhammer ℂ n).eval (-(1 / 2) - 1 / 2 - 2 * (n : ℂ)) = Nat.fib (n + 1) := by
  set a : ℝ := Real.sqrt φ
  have ha2 : a ^ 2 = φ := Real.sq_sqrt Real.goldenRatio_pos.le
  have ha : 0 < a := Real.sqrt_pos.mpr Real.goldenRatio_pos
  have hb2 : a⁻¹ ^ 2 = -ψ := by rw [inv_pow, ha2, Real.inv_goldenRatio]
  set x : ℂ := (a : ℂ) + (a⁻¹ : ℝ) * I
  set y : ℂ := (a : ℂ) - (a⁻¹ : ℝ) * I
  have hx : x ≠ 0 := fun h => by have := congrArg re h; simp [x] at this; linarith
  have hy : y ≠ 0 := fun h => by have := congrArg re h; simp [y] at this; linarith
  have hab : (a : ℂ) * (a⁻¹ : ℝ) = 1 := by
    rw [← ofReal_mul, mul_inv_cancel₀ ha.ne', ofReal_one]
  have hc2 : (a : ℂ) ^ 2 = φ := by rw [← ofReal_pow, ha2]
  have hd2 : ((a⁻¹ : ℝ) : ℂ) ^ 2 = -ψ := by rw [← ofReal_pow, hb2, ofReal_neg]
  have hsum : (φ : ℂ) + ψ = 1 := by rw [← ofReal_add, Real.goldenRatio_add_goldenConj, ofReal_one]
  have hx2 : x ^ 2 = 1 + 2 * I := by
    simp only [x]
    linear_combination hc2 + 2 * I * hab + ((a⁻¹ : ℝ) : ℂ) ^ 2 * I_sq - hd2 + hsum
  have hy2 : y ^ 2 = 1 - 2 * I := by
    simp only [y]
    linear_combination hc2 - 2 * I * hab + ((a⁻¹ : ℝ) : ℂ) ^ 2 * I_sq - hd2 + hsum
  have h := carlsonRPolynomial_chebyshevU n hx hy
  rw [hx2, hy2] at h
  rw [h]
  have hp : (x + y) / 2 = a := by simp only [x, y]; ring
  have hm : (x - y) / 2 = (a⁻¹ : ℝ) * I := by simp only [x, y]; ring
  have hxy : x * y = Real.sqrt 5 := by
    simp only [x, y]
    rw [← Real.goldenRatio_sub_goldenConj, ofReal_sub]
    linear_combination hc2 - ((a⁻¹ : ℝ) : ℂ) ^ 2 * I_sq + hd2
  have hfib := Real.coe_fib_eq (n + 1)
  rw [hp, hm, hxy, show 2 * n + 2 = 2 * (n + 1) by ring, pow_mul, pow_mul, hc2, mul_pow, I_sq, hd2,
    show (-(ψ : ℂ)) * (-1) = ψ by ring]
  exact_mod_cast hfib.symm

/-- The half-angle nodes: with `u = e^{iθ/2}`, `(u + u⁻¹)² = 2(cos θ + 1)` and
`(u - u⁻¹)² = 2(cos θ - 1)`. -/
theorem exp_half_add_inv_sq (θ : ℂ) :
    (exp (θ / 2 * I) + (exp (θ / 2 * I))⁻¹) ^ 2 = 2 * (cos θ + 1) ∧
      (exp (θ / 2 * I) - (exp (θ / 2 * I))⁻¹) ^ 2 = 2 * (cos θ - 1) := by
  have hu := exp_ne_zero (θ / 2 * I)
  have hc : cos θ = (exp (θ / 2 * I) ^ 2 + (exp (θ / 2 * I) ^ 2)⁻¹) / 2 := by
    rw [cos_eq_exp_add_inv, ← exp_nat_mul]; push_cast; ring_nf
  rw [hc]
  constructor <;> field_simp <;> ring

/-- **Exercise 7.1-12** (even degree), division-free:
`(2n)! C₂ₙ^ν(cos (θ/2)) = (-1)ⁿ (ν)ₙ 2ⁿ Nₙ(1/2 - ν - n, 1/2 - n; cos θ + 1, cos θ - 1)`.
Dividing by `(1 - ν - 2n)ₙ = (-1)ⁿ (ν + n)ₙ` gives Carlson's
`2ⁿ (ν)₂ₙ/(2n)! Rₙ(1/2 - ν - n, 1/2 - n; cos θ + 1, cos θ - 1) = C₂ₙ^ν(cos (θ/2))`. -/
theorem factorial_mul_eval_gegenbauer_two_mul_cos_half (ν θ : ℂ) (n : ℕ) :
    ((2 * n).factorial : ℂ) * (gegenbauer ν (2 * n)).eval (cos (θ / 2)) =
      (-1) ^ n * (ascPochhammer ℂ n).eval ν * 2 ^ n *
        carlsonRPolynomialNumerator₂ n (1 / 2 - ν - n) (1 / 2 - n) (cos θ + 1) (cos θ - 1) := by
  have hu := exp_ne_zero (θ / 2 * I)
  rw [cos_eq_exp_add_inv, factorial_mul_eval_gegenbauer ν _ hu,
    carlsonRPolynomialNumerator₂_firstQuadratic_even_linear, (exp_half_add_inv_sq θ).1,
    (exp_half_add_inv_sq θ).2, carlsonRPolynomialNumerator₂_smul]
  ring

/-- **Exercise 7.1-12** (odd degree), division-free:
`(2n + 1)! C₂ₙ₊₁^ν(cos (θ/2)) =
(-1)ⁿ (ν)ₙ₊₁ 2ⁿ⁺¹ cos (θ/2) Nₙ(1/2 - ν - n, -1/2 - n; cos θ + 1, cos θ - 1)`. -/
theorem factorial_mul_eval_gegenbauer_two_mul_add_one_cos_half (ν θ : ℂ) (n : ℕ) :
    ((2 * n + 1).factorial : ℂ) * (gegenbauer ν (2 * n + 1)).eval (cos (θ / 2)) =
      (-1) ^ n * (ascPochhammer ℂ (n + 1)).eval ν * 2 ^ (n + 1) * cos (θ / 2) *
        carlsonRPolynomialNumerator₂ n (1 / 2 - ν - n) (-1 / 2 - n) (cos θ + 1) (cos θ - 1) := by
  have hu := exp_ne_zero (θ / 2 * I)
  have hc := cos_eq_exp_add_inv (θ / 2)
  rw [hc, factorial_mul_eval_gegenbauer ν _ hu,
    carlsonRPolynomialNumerator₂_firstQuadratic_odd_linear, (exp_half_add_inv_sq θ).1,
    (exp_half_add_inv_sq θ).2, carlsonRPolynomialNumerator₂_smul]
  ring

/-- **Exercise 7.2-1** (Gegenbauer biorthogonality): if `ν + 1/2`, `ν` and `2ν` are not
nonpositive integers and the circle `C(c, R)` encloses `±1`, then
`(2πi)⁻¹ ∮ C_m^{ν-1/2}(y) R_{-n-1}(ν + n, ν + n; y + 1, y - 1) dy = δₘₙ 2ⁿ (ν - 1/2)ₙ/n!`,
where the second-kind function is `jacobiSecondKind (ν - 1) (ν - 1) (-1) 1 n`. -/
theorem circleIntegral_gegenbauer_mul_jacobiSecondKind {ν : ℂ}
    (hν₁ : ∀ m : ℕ, (ascPochhammer ℂ m).eval (ν - 1 / 2) ≠ 0)
    (hν₂ : ∀ m : ℕ, (ascPochhammer ℂ m).eval ν ≠ 0) (h2ν : IsGammaRegular (2 * ν)) (m n : ℕ)
    {c : ℂ} {R : ℝ} (hR : 0 < R) (hz : Set.range (pair (-1) 1) ⊆ Metric.ball c R) :
    (2 * (Real.pi : ℂ) * I)⁻¹ * (∮ y in C(c, R), (gegenbauer (ν - 1 / 2) m).eval y *
      jacobiSecondKind (ν - 1) (ν - 1) (-1) 1 n y) =
        if m = n then 2 ^ n * (ascPochhammer ℂ n).eval (ν - 1 / 2) / n.factorial else 0 := by
  have hc : IsGammaRegular (ν - 1 + (ν - 1) + 2) := by
    rw [show ν - 1 + (ν - 1) + 2 = 2 * ν by ring]; exact h2ν
  have h := circleIntegral_jacobiOn_mul_jacobiSecondKind (ν - 1) (ν - 1) (-1) 1 hc m n hR hz
  have hf : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
  have hG (y : ℂ) : (gegenbauer (ν - 1 / 2) m).eval y =
      2 ^ m * (ascPochhammer ℂ m).eval (ν - 1 / 2) / m.factorial *
        (jacobiOn (ν - 1) (ν - 1) (-1) 1 m).eval y := by
    have hJ := eval_jacobiOn_gegenbauer ν y m (hν₁ m) (hν₂ m)
    rw [div_mul_eq_mul_div, eq_div_iff hf]
    linear_combination -hJ
  have hint : (∮ y in C(c, R), (gegenbauer (ν - 1 / 2) m).eval y *
      jacobiSecondKind (ν - 1) (ν - 1) (-1) 1 n y) =
      2 ^ m * (ascPochhammer ℂ m).eval (ν - 1 / 2) / m.factorial *
        ∮ y in C(c, R), (jacobiOn (ν - 1) (ν - 1) (-1) 1 m).eval y *
          jacobiSecondKind (ν - 1) (ν - 1) (-1) 1 n y := by
    rw [← circleIntegral.integral_const_mul]
    congr 1; funext y; rw [hG]; ring
  rw [hint, mul_left_comm, h]
  split_ifs with hmn
  · subst hmn; ring
  · ring

/-- **Exercise 7.8-1**, Rodrigues' formula for Legendre polynomials:
`Dⁿ (x² - 1)ⁿ = 2ⁿ n! Pₙ(x)`, with `Pₙ = Cₙ^{1/2}`. -/
theorem iterate_derivative_X_sq_sub_one_pow (n : ℕ) :
    derivative^[n] (((X : ℂ[X]) ^ 2 - 1) ^ n) =
      C (2 ^ n * (n.factorial : ℂ)) * gegenbauer (1 / 2 : ℂ) n := by
  have haff : (X : ℂ[X]) ^ 2 - 1 =
      ((C (-4 : ℂ)) * X * (1 - X)).comp (C (-1 / 2) * X + C (1 / 2)) := by
    simp only [mul_comp, C_comp, X_comp, sub_comp, one_comp]
    apply Polynomial.funext; intro x; simp; ring
  have hlin : C (algebraMap ℚ ℂ (1 / 2)) * (1 - X) = C (-1 / 2 : ℂ) * X + C (1 / 2) := by
    simp only [map_div₀, map_one, map_ofNat]
    apply Polynomial.funext; intro x; simp; ring
  rw [haff, ← pow_comp, iterate_derivative_comp_affine, mul_pow, mul_pow, ← C_pow, mul_assoc,
    iterate_derivative_C_mul, show (X : ℂ[X]) ^ n * (1 - X) ^ n = X ^ (0 + n) * (1 - X) ^ (0 + n) by
      simp, shiftedJacobi_rodrigues_nat 0 0 n, gegenbauer_half_param, jacobi, hlin]
  simp only [pow_zero, mul_one, Nat.cast_zero, mul_comp, C_comp, ← mul_assoc, ← C_mul]
  congr 2
  rw [← mul_pow]; norm_num

/-- `a (a + 1)ₖ = (a)ₖ (a + k)`. -/
theorem mul_ascPochhammer_add_one (a : ℂ) (k : ℕ) :
    a * (ascPochhammer ℂ k).eval (a + 1) = (ascPochhammer ℂ k).eval a * (a + k) := by
  rw [← ascPochhammer_succ_eval, ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add,
    eval_X, eval_one]

/-- A terminating Gauss function with first parameter `-(m + 1)`, written as a finite sum over
`range (m + 2)`, and with first parameter `-m` extended by a vanishing term. -/
private theorem ordinaryHypergeometric_neg_natCast_succ_range (m : ℕ) (b c y : ℂ) :
    ordinaryHypergeometric (-(m : ℂ)) b c y = ∑ k ∈ range (m + 2),
      ((k.factorial : ℂ)⁻¹ * (ascPochhammer ℂ k).eval (-(m : ℂ)) * (ascPochhammer ℂ k).eval b *
        ((ascPochhammer ℂ k).eval c)⁻¹) * y ^ k := by
  rw [ordinaryHypergeometric_neg_natCast, Finset.sum_range_succ (n := m + 1)]
  rw [(ascPochhammer_eval_eq_zero_iff _ _).mpr ⟨m, by omega, by simp⟩]
  simp

/-- The contiguous relation behind `2T₂ₙ = U₂ₙ - U₂ₙ₋₂`:
`F(-n, n + 1; c; y) + F(1 - n, n; c; y) = 2F(-n, n; c; y)` with `n = m + 1`. -/
theorem ordinaryHypergeometric_even_contiguous (m : ℕ) (c y : ℂ) :
    ordinaryHypergeometric (-((m + 1 : ℕ) : ℂ)) (m + 2) c y +
        ordinaryHypergeometric (-(m : ℂ)) (m + 1) c y =
      2 * ordinaryHypergeometric (-((m + 1 : ℕ) : ℂ)) (m + 1) c y := by
  rw [ordinaryHypergeometric_neg_natCast, ordinaryHypergeometric_neg_natCast_succ_range,
    ordinaryHypergeometric_neg_natCast, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl fun k _ => ?_
  have hA := mul_ascPochhammer_add_one ((m : ℂ) + 1) k
  have hB := mul_ascPochhammer_add_one (-((m : ℂ) + 1)) k
  rw [show (m : ℂ) + 1 + 1 = m + 2 by ring, show -((m : ℂ) + 1) + 1 = -m by ring] at *
  have hm : (m : ℂ) + 1 ≠ 0 := by exact_mod_cast m.succ_ne_zero
  push_cast
  generalize (ascPochhammer ℂ k).eval (-((m : ℂ) + 1)) = P at *
  generalize (ascPochhammer ℂ k).eval ((m : ℂ) + 1) = Q at *
  generalize (ascPochhammer ℂ k).eval ((m : ℂ) + 2) = R at *
  generalize (ascPochhammer ℂ k).eval (-(m : ℂ)) = S at *
  have key : P * R + S * Q = 2 * P * Q := by
    refine mul_left_cancel₀ hm ?_
    linear_combination P * hA - Q * hB
  linear_combination ((k.factorial : ℂ)⁻¹ * ((ascPochhammer ℂ k).eval c)⁻¹ * y ^ k) * key

/-- The contiguous relation behind `2T₂ₙ₊₁ = U₂ₙ₊₁ - U₂ₙ₋₁`, with `n = m + 1`:
`(n + 1) F(-n, n + 2; c; y) + n F(1 - n, n + 1; c; y) = (2n + 1) F(-n, n + 1; c; y)`. -/
theorem ordinaryHypergeometric_odd_contiguous (m : ℕ) (c y : ℂ) :
    (m + 2) * ordinaryHypergeometric (-((m + 1 : ℕ) : ℂ)) (m + 3) c y +
        (m + 1) * ordinaryHypergeometric (-(m : ℂ)) (m + 2) c y =
      (2 * m + 3) * ordinaryHypergeometric (-((m + 1 : ℕ) : ℂ)) (m + 2) c y := by
  rw [ordinaryHypergeometric_neg_natCast, ordinaryHypergeometric_neg_natCast_succ_range,
    ordinaryHypergeometric_neg_natCast, mul_sum, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hA := mul_ascPochhammer_add_one ((m : ℂ) + 2) k
  have hB := mul_ascPochhammer_add_one (-((m : ℂ) + 1)) k
  rw [show (m : ℂ) + 2 + 1 = m + 3 by ring, show -((m : ℂ) + 1) + 1 = -m by ring] at *
  push_cast
  generalize (ascPochhammer ℂ k).eval (-((m : ℂ) + 1)) = P at *
  generalize (ascPochhammer ℂ k).eval ((m : ℂ) + 2) = Q at *
  generalize (ascPochhammer ℂ k).eval ((m : ℂ) + 3) = R at *
  generalize (ascPochhammer ℂ k).eval (-(m : ℂ)) = S at *
  linear_combination ((k.factorial : ℂ)⁻¹ * ((ascPochhammer ℂ k).eval c)⁻¹ * y ^ k) *
    (P * hA - Q * hB)

/-- `cos (x + nπ) = (-1)ⁿ cos x` for complex `x`. -/
theorem cos_add_nat_mul_pi_complex (x : ℂ) (n : ℕ) :
    cos (x + n * Real.pi) = (-1) ^ n * cos x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, cos_add_pi, ih, pow_succ]; ring

/-- `Uₘ(x) = Cₘ¹(x)` evaluated, for a natural index. -/
private theorem eval_U_eq_gegenbauer (m : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ (m : ℤ)).eval x = (gegenbauer (1 : ℂ) m).eval x := by
  rw [gegenbauer_one_param_eq_chebyshev_U]

/-- `U₂ₙ(x) = (-1)ⁿ ₂F₁(-n, n + 1; 1/2; x²)`. -/
private theorem eval_U_two_mul (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ ((2 * n : ℕ) : ℤ)).eval x =
      (-1) ^ n * ordinaryHypergeometric (-(n : ℂ)) (n + 1) (1 / 2) (x ^ 2) := by
  rw [eval_U_eq_gegenbauer, eval_gegenbauer_two_mul_eq_hypergeometric, ascPochhammer_eval_one]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [add_comm (1 : ℂ)]
  field_simp

/-- `U₂ₙ₊₁(x) = (-1)ⁿ (n + 1) 2x ₂F₁(-n, n + 2; 3/2; x²)`. -/
private theorem eval_U_two_mul_add_one (n : ℕ) (x : ℂ) :
    (Chebyshev.U ℂ ((2 * n + 1 : ℕ) : ℤ)).eval x =
      (-1) ^ n * (n + 1) * (2 * x) * ordinaryHypergeometric (-(n : ℂ)) (n + 2) (3 / 2) (x ^ 2) := by
  rw [eval_U_eq_gegenbauer, eval_gegenbauer_two_mul_add_one_eq_hypergeometric,
    ascPochhammer_eval_one, Nat.factorial_succ, show (1 : ℂ) + n + 1 = n + 2 by ring]
  have : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  push_cast
  field_simp

/-- **Exercise 6.9-10** (even multiple, `cos²` form): `cos 2nθ = (-1)ⁿ ₂F₁(-n, n; 1/2; cos² θ)`. -/
theorem cos_two_mul_mul_eq_hypergeometric_cos (θ : ℂ) (n : ℕ) :
    cos (2 * n * θ) = (-1) ^ n * ordinaryHypergeometric (-(n : ℂ)) n (1 / 2) (cos θ ^ 2) := by
  rcases n with _ | m
  · rw [ordinaryHypergeometric_neg_natCast]; simp
  have hT := congrArg (eval (cos θ)) (Chebyshev.two_mul_T_eq_U_sub_U (R := ℂ) ((2 * m : ℕ) : ℤ))
  simp only [eval_mul, eval_sub, eval_ofNat] at hT
  rw [show ((2 * m : ℕ) : ℤ) + 2 = ((2 * (m + 1) : ℕ) : ℤ) by push_cast; ring, eval_U_two_mul,
    eval_U_two_mul, Chebyshev.T_complex_cos] at hT
  have hc := ordinaryHypergeometric_even_contiguous m (1 / 2) (cos θ ^ 2)
  push_cast at hT hc ⊢
  rw [show (m : ℂ) + 1 + 1 = m + 2 by ring] at hT
  linear_combination hT / 2 + (-1) ^ (m + 1) * hc / 2

/-- **Exercise 6.9-10** (even multiple, `sin²` form): `cos 2nθ = ₂F₁(-n, n; 1/2; sin² θ)`. -/
theorem cos_two_mul_mul_eq_hypergeometric_sin (θ : ℂ) (n : ℕ) :
    cos (2 * n * θ) = ordinaryHypergeometric (-(n : ℂ)) n (1 / 2) (sin θ ^ 2) := by
  have h := cos_two_mul_mul_eq_hypergeometric_cos (Real.pi / 2 - θ) n
  rw [cos_pi_div_two_sub, show 2 * (n : ℂ) * (Real.pi / 2 - θ) = -(2 * n * θ) + n * Real.pi by
    ring, cos_add_nat_mul_pi_complex, cos_neg] at h
  have h1 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h1 h

/-- **Exercise 6.9-10** (odd multiple, `cos²` form):
`cos (2n + 1)θ = (-1)ⁿ (2n + 1) cos θ ₂F₁(-n, n + 1; 3/2; cos² θ)`. -/
theorem cos_two_mul_add_one_mul_eq_hypergeometric_cos (θ : ℂ) (n : ℕ) :
    cos ((2 * n + 1) * θ) = (-1) ^ n * (2 * n + 1) * cos θ *
      ordinaryHypergeometric (-(n : ℂ)) (n + 1) (3 / 2) (cos θ ^ 2) := by
  rcases n with _ | m
  · rw [ordinaryHypergeometric_neg_natCast]; simp
  have hT := congrArg (eval (cos θ))
    (Chebyshev.two_mul_T_eq_U_sub_U (R := ℂ) ((2 * m + 1 : ℕ) : ℤ))
  simp only [eval_mul, eval_sub, eval_ofNat] at hT
  rw [show ((2 * m + 1 : ℕ) : ℤ) + 2 = ((2 * (m + 1) + 1 : ℕ) : ℤ) by push_cast; ring,
    eval_U_two_mul_add_one, eval_U_two_mul_add_one, Chebyshev.T_complex_cos] at hT
  have hc := ordinaryHypergeometric_odd_contiguous m (3 / 2) (cos θ ^ 2)
  push_cast at hT hc ⊢
  rw [show (m : ℂ) + 1 + 2 = m + 3 by ring, show (m : ℂ) + 1 + 1 = m + 2 by ring] at hT
  rw [show 2 * ((m : ℂ) + 1) + 1 = 2 * m + 3 by ring] at hT ⊢
  rw [show (m : ℂ) + 1 + 1 = m + 2 by ring]
  linear_combination hT / 2 + (-1) ^ (m + 1) * cos θ * hc

/-- **Exercise 6.9-11** (odd multiple, `sin²` form):
`sin (2n + 1)θ = (2n + 1) sin θ ₂F₁(-n, n + 1; 3/2; sin² θ)`. -/
theorem sin_two_mul_add_one_mul_eq_hypergeometric_sin (θ : ℂ) (n : ℕ) :
    sin ((2 * n + 1) * θ) = (2 * n + 1) * sin θ *
      ordinaryHypergeometric (-(n : ℂ)) (n + 1) (3 / 2) (sin θ ^ 2) := by
  have h := cos_two_mul_add_one_mul_eq_hypergeometric_cos (Real.pi / 2 - θ) n
  rw [cos_pi_div_two_sub, show (2 * (n : ℂ) + 1) * (Real.pi / 2 - θ) =
    Real.pi / 2 - (2 * n + 1) * θ + n * Real.pi by ring, cos_add_nat_mul_pi_complex,
    cos_pi_div_two_sub] at h
  have h1 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ h1 (by rw [h]; ring)

/-- **Exercise 7.8-1**, Rodrigues' formula for Gegenbauer polynomials, on the principal branch:
if `x ± 1` lie in the slit plane and `(ν)ₙ, (ν + 1/2)ₙ, (2ν + n)ₙ ≠ 0`, then
`(2ν)ₙ Dⁿ[(x + 1)^{ν-1/2+n} (x - 1)^{ν-1/2+n}] =
2ⁿ n! (ν + 1/2)ₙ (x + 1)^{ν-1/2} (x - 1)^{ν-1/2} Cₙ^ν(x)`. Carlson writes the powers as powers
of `x² - 1`. -/
theorem iteratedDeriv_gegenbauer_rodrigues (ν : ℂ) (n : ℕ) {x : ℂ}
    (hr : x + 1 ∈ slitPlane) (hs : x - 1 ∈ slitPlane)
    (hν : (ascPochhammer ℂ n).eval ν ≠ 0) (hν' : (ascPochhammer ℂ n).eval (ν + 1 / 2) ≠ 0)
    (h2 : (ascPochhammer ℂ n).eval (2 * ν + n) ≠ 0) :
    (ascPochhammer ℂ n).eval (2 * ν) *
        iteratedDeriv n (fun w => (w + 1) ^ (ν - 1 / 2 + n) * (w - 1) ^ (ν - 1 / 2 + n)) x =
      2 ^ n * n.factorial * (ascPochhammer ℂ n).eval (ν + 1 / 2) *
        ((x + 1) ^ (ν - 1 / 2) * (x - 1) ^ (ν - 1 / 2) * (gegenbauer ν n).eval x) := by
  have hR := iteratedDeriv_sub_cpow_mul_sub_cpow (ν - 1 / 2) (ν - 1 / 2) (-1) 1 n
    (by rwa [sub_neg_eq_add]) hs
    (by rw [show ν - 1 / 2 + (ν - 1 / 2) + n + 1 = 2 * ν + n by ring]; exact h2)
  simp only [sub_neg_eq_add] at hR
  rw [hR, show ν - 1 / 2 + (ν - 1 / 2) + n + 1 = 2 * ν + n by ring]
  have hJ := eval_jacobiOn_gegenbauer (ν + 1 / 2) x n
    (by rw [show ν + 1 / 2 - 1 / 2 = ν by ring]; exact hν) hν'
  rw [show ν + 1 / 2 - 1 = ν - 1 / 2 by ring, show ν + 1 / 2 - 1 / 2 = ν by ring] at hJ
  have hd := ascPochhammer_eval_double ν n
  rw [two_mul n, ascPochhammer_add_eval] at hd
  have h4 : (4 : ℂ) ^ n = 2 ^ n * 2 ^ n := by rw [← mul_pow]; norm_num
  linear_combination ((x + 1) ^ (ν - 1 / 2) * (x - 1) ^ (ν - 1 / 2)) *
    ((jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 n).eval x * hd + 2 ^ n *
      (ascPochhammer ℂ n).eval (ν + 1 / 2) * hJ +
      (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 n).eval x * (ascPochhammer ℂ n).eval ν *
        (ascPochhammer ℂ n).eval (ν + 1 / 2) * h4)

end Carlson.TwoVariable
