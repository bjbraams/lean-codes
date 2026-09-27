/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Gegenbauer
public import Carlson.Jacobi.Carlson
public import Carlson.Jacobi.Laguerre
public import Carlson.TwoVariable.Quadratic.Polynomial
public import Carlson.TwoVariable.BilateralGenerating
public import Carlson.R.ContourRepresentation
public import Carlson.RPolynomial.Growth

/-!
# Gegenbauer polynomials as R-polynomials, and Gegenbauer's product formula

Carlson's formula (6.7-21) identifies the Gegenbauer polynomial with a two-node R-polynomial,
`n! C_n^ν((w + w⁻¹)/2) = (2ν)ₙ Rₙ(ν, ν; w, w⁻¹)`; here it is derived from the Jacobi
identification of Chapter 7 and the division-free second quadratic transformation (6.10-3),
first where `(2ν)_{2n} ≠ 0` and then for every parameter by continuity. It yields the
generating function of the Gegenbauer polynomials and Carlson's bound on the unit circle.

Meixner's formula (Corollary 6.11-2) at `a = β = ν`, `c = 2ν` and nodes on the unit circle
gives Ossicini's formula (Corollary 6.11-3). Comparing its power series in `t` with the
Dirichlet-average representation of the same R-function, expanded by the generating function,
gives Gegenbauer's product formula (Theorem 6.11-4).

## Main results

* `Carlson.TwoVariable.factorial_mul_eval_gegenbauer`: formula (6.7-21).
* `Carlson.TwoVariable.eval_gegenbauer_one`: `C_n^ν(1) = (2ν)ₙ / n!`.
* `Carlson.TwoVariable.hasSum_gegenbauer_mul_pow`: the generating function.
* `Carlson.TwoVariable.hasSum_ossicini`: Ossicini's formula (Corollary 6.11-3).
* `Carlson.TwoVariable.gegenbauer_product_formula`: Gegenbauer's product formula
  (Theorem 6.11-4).

## Implementation notes

Ossicini's formula and the product formula are stated for real angles `θ, φ` and
`re ν > 0`, as in Carlson's Theorem 6.11-4; Carlson's Corollary 6.11-3 also allows complex
angles with `|t| < exp(-|Im θ| - |Im φ|)`.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §§6.7, 6.11.
-/

open Dirichlet
open Complex Set Filter MeasureTheory Polynomial
open scoped Topology
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Gegenbauer polynomials as two-node Carlson numerators (Carlson (6.7-21)), where the
duplicated Pochhammer symbol `(2ν)_{2n}` does not vanish. -/
theorem factorial_mul_eval_gegenbauer_of_ne (ν w : ℂ) (hw : w ≠ 0) (n : ℕ)
    (h2n : (ascPochhammer ℂ (2 * n)).eval (2 * ν) ≠ 0) :
    (n.factorial : ℂ) * (gegenbauer ν n).eval ((w + w⁻¹) / 2) =
      carlsonRPolynomialNumerator₂ n ν ν w w⁻¹ := by
  set x := (w + w⁻¹) / 2
  set p : ℂ := w ^ ((2 : ℂ)⁻¹)
  have hp2 : p ^ 2 = w := cpow_ofNat_inv_pow w 2
  have hp0 : p ≠ 0 := fun h => hw (by rw [← hp2, h]; ring)
  have hq2 : p⁻¹ ^ 2 = w⁻¹ := by rw [inv_pow, hp2]
  have hplus : (p + p⁻¹) ^ 2 = 2 * (x + 1) := by
    simp only [x]; rw [← hp2]; field_simp; ring
  have hminus : (p - p⁻¹) ^ 2 = 2 * (x - 1) := by
    simp only [x]; rw [← hp2]; field_simp; ring
  set N := carlsonRPolynomialNumerator₂ n ν ν w w⁻¹
  set M := carlsonRPolynomialNumerator₂ n (1 / 2 - ν - n) (1 / 2 - ν - n) (x + 1) (x - 1)
  set J := (jacobi (ν - 1 / 2) (ν - 1 / 2) n).eval x
  set G := (gegenbauer ν n).eval x
  set A := (ascPochhammer ℂ n).eval (2 * ν)
  set Bn := (ascPochhammer ℂ n).eval (2 * ν + n)
  set V := (ascPochhammer ℂ n).eval ν
  set H := (ascPochhammer ℂ n).eval (ν + 1 / 2)
  set s : ℂ := (-1) ^ n
  set T : ℂ := 2 ^ n
  set F : ℂ := (n.factorial : ℂ)
  have hs : s * s = 1 := by simp only [s]; rw [← mul_pow]; norm_num
  have hq : (ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) * N = V * (T * M) := by
    have h := carlsonRPolynomialNumerator₂_secondQuadratic n ν p p⁻¹
    rw [hp2, hq2, hplus, hminus, carlsonRPolynomialNumerator₂_smul] at h
    exact h
  have hrefl : (ascPochhammer ℂ n).eval (1 - 2 * ν - 2 * n) = s * Bn := by
    rw [show 1 - 2 * ν - 2 * (n : ℂ) = 1 - (2 * ν + n) - n by ring]
    exact ascPochhammer_eval_reflect _ _
  have hj : T * F * J = s * M := by
    have h := factorial_mul_eval_jacobi (ν - 1 / 2) (ν - 1 / 2) x n
    rw [show -(ν - 1 / 2) - (n : ℂ) = 1 / 2 - ν - n by ring] at h
    rw [← h]
  have hg : H * G = A * J := by
    have h := congrArg (Polynomial.eval x) (pochhammer_mul_gegenbauer ν n)
    simpa only [eval_mul, eval_C] using h
  have hdup : (ascPochhammer ℂ (2 * n)).eval (2 * ν) = T * T * V * H := by
    rw [ascPochhammer_eval_double, show (4 : ℂ) ^ n = T * T by
      simp only [T]; rw [← mul_pow]; norm_num]
  have hadd : (ascPochhammer ℂ (2 * n)).eval (2 * ν) = A * Bn := by
    rw [two_mul n, ascPochhammer_add_eval]
  -- solve the linear system
  have hM : M = s * (T * F * J) := by rw [hj, ← mul_assoc, hs, one_mul]
  have hBN : Bn * N = V * T * T * F * J := by
    have h1 : s * (Bn * N) = s * (V * T * T * F * J) := by
      rw [← mul_assoc, ← hrefl, hq, hM]
      ring
    exact mul_left_cancel₀ (by simp [s]) h1
  apply mul_left_cancel₀ h2n
  calc (ascPochhammer ℂ (2 * n)).eval (2 * ν) * (F * G)
      = T * T * V * F * (H * G) := by rw [hdup]; ring
    _ = T * T * V * F * (A * J) := by rw [hg]
    _ = A * (Bn * N) := by rw [hBN]; ring
    _ = (ascPochhammer ℂ (2 * n)).eval (2 * ν) * N := by rw [hadd]; ring


/-- **Carlson (6.7-21)**: Gegenbauer polynomials as two-node Carlson numerators,
`n! C_n^ν((w + w⁻¹)/2) = (2ν)ₙ Rₙ(ν, ν; w, w⁻¹)`, for every parameter `ν` and every nonzero
`w`. With `w = e^{iθ}` this is `C_n^ν(cos θ) = C_n^ν(1) Rₙ(ν, ν; e^{iθ}, e^{-iθ})`. -/
theorem factorial_mul_eval_gegenbauer (ν w : ℂ) (hw : w ≠ 0) (n : ℕ) :
    (n.factorial : ℂ) * (gegenbauer ν n).eval ((w + w⁻¹) / 2) =
      carlsonRPolynomialNumerator₂ n ν ν w w⁻¹ := by
  set x := (w + w⁻¹) / 2
  have hL : Continuous fun ν : ℂ => (n.factorial : ℂ) * (gegenbauer ν n).eval x := by
    unfold gegenbauer shiftedGegenbauer
    simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
    fun_prop
  have hR : Continuous fun ν : ℂ => carlsonRPolynomialNumerator₂ n ν ν w w⁻¹ := by
    unfold carlsonRPolynomialNumerator₂
    fun_prop
  have hbad : {ν : ℂ | (ascPochhammer ℂ (2 * n)).eval (2 * ν) = 0}.Countable := by
    refine (Set.countable_range fun k : ℕ => -(k : ℂ) / 2).mono ?_
    intro ν hν
    obtain ⟨k, -, hk⟩ := (ascPochhammer_eval_eq_zero_iff _ _).1 hν
    exact ⟨k, by simp only; rw [hk]; ring⟩
  have hdense := hbad.dense_compl ℂ
  have h := hL.ext_on hdense hR fun ν hν =>
    factorial_mul_eval_gegenbauer_of_ne ν w hw n hν
  exact congrFun h ν


/-- `C_n^ν(1) = (2ν)ₙ / n!`. -/
theorem eval_gegenbauer_one (ν : ℂ) (n : ℕ) :
    (gegenbauer ν n).eval 1 = (ascPochhammer ℂ n).eval (2 * ν) / n.factorial := by
  have h := factorial_mul_eval_gegenbauer ν 1 one_ne_zero n
  rw [inv_one, show ((1 : ℂ) + 1) / 2 = 1 by norm_num] at h
  have hN : carlsonRPolynomialNumerator₂ n ν ν 1 1 = (ascPochhammer ℂ n).eval (2 * ν) := by
    rw [two_mul, ascPochhammer_eval_add, carlsonRPolynomialNumerator₂]
    refine Finset.sum_congr rfl fun ij _ => ?_
    simp only [one_pow, mul_one]; ring
  rw [hN] at h
  rw [eq_div_iff (by exact_mod_cast n.factorial_ne_zero), ← h]; ring

/-- The generating function of the Gegenbauer polynomials, in the factored form
`∑ C_m^ν((w + w⁻¹)/2) t^m = (1 - t w)^(-ν) (1 - t/w)^(-ν)` (Carlson (6.7-19)). -/
theorem hasSum_gegenbauer_mul_pow (ν w t : ℂ) (hw : w ≠ 0) (h₁ : ‖t * w‖ < 1)
    (h₂ : ‖t * w⁻¹‖ < 1) :
    HasSum (fun m : ℕ => (gegenbauer ν m).eval ((w + w⁻¹) / 2) * t ^ m)
      ((1 - t * w) ^ (-ν) * (1 - t * w⁻¹) ^ (-ν)) := by
  have h := hasSum_carlsonRPolynomialNumerator_div_factorial (pair ν ν) (pair w w⁻¹) t
    (fun i => by fin_cases i; exacts [h₁, h₂])
  rw [carlsonRGeneratingKernel, Fin.prod_univ_two] at h
  simp only [pair_zero, pair_one, one_div, ← cpow_neg] at h
  refine h.congr_fun fun m => ?_
  rw [carlsonRPolynomialNumerator_pair, ← factorial_mul_eval_gegenbauer ν w hw m]
  field_simp [Nat.cast_ne_zero.mpr m.factorial_ne_zero]

/-- On the unit circle, Carlson's estimate bounds the Gegenbauer polynomials:
`‖C_m^ν((w + w⁻¹)/2)‖ ≤ (2‖ν‖)_m / m!` for `‖w‖ = 1`. -/
theorem norm_eval_gegenbauer_le (ν w : ℂ) (hw : ‖w‖ = 1) (m : ℕ) :
    ‖(gegenbauer ν m).eval ((w + w⁻¹) / 2)‖ ≤
      (ascPochhammer ℝ m).eval (2 * ‖ν‖) / m.factorial := by
  have hw0 : w ≠ 0 := fun h => by simp [h] at hw
  have h := norm_carlsonRPolynomialNumerator_le_sum_norm m (pair ν ν) (pair w w⁻¹) zero_le_one
    (fun i => by fin_cases i <;> simp [pair, hw])
  rw [carlsonRPolynomialNumerator_pair, ← factorial_mul_eval_gegenbauer ν w hw0 m, norm_mul,
    Complex.norm_natCast, one_pow, mul_one, Fin.sum_univ_two] at h
  simp only [pair_zero, pair_one] at h
  rw [le_div_iff₀ (by exact_mod_cast m.factorial_pos), ← two_mul] at *
  linarith


/-- `(e^{iθ} + e^{-iθ})/2 = cos θ`. -/
theorem exp_add_inv_div_two (θ : ℂ) : (exp (θ * I) + (exp (θ * I))⁻¹) / 2 = cos θ := by
  rw [← exp_neg, ← neg_mul, ← two_cos]; ring

/-- `(1 - t e^{iψ})(1 - t e^{-iψ}) = 1 - 2 t cos ψ + t²`. -/
theorem one_sub_mul_exp_mul (t ψ : ℂ) :
    (1 - t * exp (ψ * I)) * (1 - t * (exp (ψ * I))⁻¹) = 1 - 2 * t * cos ψ + t ^ 2 := by
  have h := two_cos (x := ψ)
  rw [neg_mul, exp_neg] at h
  have h0 : exp (ψ * I) ≠ 0 := exp_ne_zero _
  linear_combination t * h + t ^ 2 * (mul_inv_cancel₀ h0)

/-- The regularized Ossicini series: for `re ν > 0`, real `θ, φ` and `‖t‖ < 1`,
`R_{-ν}(ν, ν; 1 - 2t cos(θ+φ) + t², 1 - 2t cos(θ-φ) + t²) / Γ(2ν)
  = ∑ tⁿ n! C_n^ν(cos θ) C_n^ν(cos φ) / Γ(2ν + n)`. -/
theorem hasSum_regOssicini {ν : ℂ} (hν : 0 < ν.re) (θ φ : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => t ^ n * n.factorial * (gegenbauer ν n).eval (cos θ) *
        (gegenbauer ν n).eval (cos φ) * (Gamma (2 * ν + n))⁻¹)
      (regCarlsonR (-ν) (pair ν ν)
        (pair (1 - 2 * t * cos (θ + φ) + t ^ 2) (1 - 2 * t * cos (θ - φ) + t ^ 2))) := by
  set a := exp ((θ : ℂ) * I)
  set b := exp ((φ : ℂ) * I)
  have ha1 : ‖a‖ = 1 := norm_exp_ofReal_mul_I θ
  have hb1 : ‖b‖ = 1 := norm_exp_ofReal_mul_I φ
  have ha0 : a ≠ 0 := exp_ne_zero _
  have hb0 : b ≠ 0 := exp_ne_zero _
  have hn : ∀ u v : ℂ, ‖u‖ = 1 → ‖v‖ = 1 → ‖t * u * v‖ < 1 := fun u v hu hv => by
    rw [norm_mul, norm_mul, hu, hv]; simpa using ht
  have ha1' : ‖a⁻¹‖ = 1 := by rw [norm_inv, ha1, inv_one]
  have hb1' : ‖b⁻¹‖ = 1 := by rw [norm_inv, hb1, inv_one]
  have h := hasSum_meixner ν ν (2 * ν) (t * a) (t * a⁻¹) b b⁻¹ hν
    (by rw [show 2 * ν - ν = ν by ring]; exact hν)
    (hn a b ha1 hb1) (hn a b⁻¹ ha1 hb1') (hn a⁻¹ b ha1' hb1) (hn a⁻¹ b⁻¹ ha1' hb1')
  rw [show 2 * ν - ν = ν by ring, show ν - ν = 0 by ring, show ν + ν - 2 * ν = 0 by ring,
    cpow_zero, cpow_zero, one_mul, one_mul] at h
  have hA : (1 - t * a * b) * (1 - t * a⁻¹ * b⁻¹) = 1 - 2 * t * cos (θ + φ) + t ^ 2 := by
    have := one_sub_mul_exp_mul t ((θ : ℂ) + φ)
    rw [add_mul, exp_add, mul_inv] at this
    rw [← this]; ring
  have hB : (1 - t * a * b⁻¹) * (1 - t * a⁻¹ * b) = 1 - 2 * t * cos (θ - φ) + t ^ 2 := by
    have := one_sub_mul_exp_mul t ((θ : ℂ) - φ)
    rw [show ((θ : ℂ) - φ) * I = θ * I + -(φ * I) by ring, exp_add, exp_neg, mul_inv,
      inv_inv] at this
    rw [← this]; ring
  rw [hA, hB] at h
  refine h.congr_fun fun n => ?_
  have hθ := factorial_mul_eval_gegenbauer ν a ha0 n
  have hφ := factorial_mul_eval_gegenbauer ν b hb0 n
  rw [exp_add_inv_div_two] at hθ hφ
  rw [carlsonRPolynomialNumerator₂_smul, ← hθ, regRPolynomial_eq_numerator₂_mul_one_div_Gamma,
    ← hφ, show ν + ν + (n : ℂ) = 2 * ν + n by ring]
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]

/-- **Ossicini's formula** (Corollary 6.11-3), for `re ν > 0`, real `θ, φ` and `‖t‖ < 1`:
`R_{-ν}(ν, ν; 1 - 2t cos(θ+φ) + t², 1 - 2t cos(θ-φ) + t²)
  = ∑ tⁿ C_n^ν(cos θ) C_n^ν(cos φ) / C_n^ν(1)`. -/
theorem hasSum_ossicini {ν : ℂ} (hν : 0 < ν.re) (θ φ : ℝ) {t : ℂ} (ht : ‖t‖ < 1) :
    HasSum (fun n : ℕ => t ^ n * (gegenbauer ν n).eval (cos θ) *
        (gegenbauer ν n).eval (cos φ) / (gegenbauer ν n).eval 1)
      (carlsonR (-ν) (pair ν ν)
        (pair (1 - 2 * t * cos (θ + φ) + t ^ 2) (1 - 2 * t * cos (θ - φ) + t ^ 2))) := by
  have h := (hasSum_regOssicini hν θ φ ht).mul_left (Gamma (2 * ν))
  rw [carlsonR, sum_pair, ← two_mul]
  refine h.congr_fun fun n => ?_
  have h2ν : 0 < (2 * ν).re := by simp; linarith
  have hP : (ascPochhammer ℂ n).eval (2 * ν) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simpa using h2ν) n
  rw [eval_gegenbauer_one, Gamma_add_nat_eq_ascPochhammer_mul h2ν]
  have hΓ := Gamma_ne_zero_of_re_pos h2ν
  field_simp [Nat.cast_ne_zero.mpr n.factorial_ne_zero]


/-- **Gegenbauer's product formula** (Theorem 6.11-4): for `re ν > 0` and real `θ, φ`,
`C_n^ν(cos θ) C_n^ν(cos φ) = C_n^ν(1) ∫₀¹ C_n^ν(u cos(θ+φ) + (1-u) cos(θ-φ)) dμ_{(ν,ν)}(u)`,
the integral being Carlson's Dirichlet average with parameters `(ν, ν)`. -/
theorem gegenbauer_product_formula {ν : ℂ} (hν : 0 < ν.re) (θ φ : ℝ) (n : ℕ) :
    (gegenbauer ν n).eval (cos θ) * (gegenbauer ν n).eval (cos φ) =
      (gegenbauer ν n).eval 1 * carlsonDirichletAverage (pair ν ν)
        (pair (cos (θ + φ)) (cos (θ - φ))) (fun x => (gegenbauer ν n).eval x) := by
  -- the interpolated real argument and its unit-circle representative
  set xr : ℝ → ℝ := fun u => u * Real.cos (θ + φ) + (1 - u) * Real.cos (θ - φ)
  have hxr : ∀ u ∈ Icc (0 : ℝ) 1, xr u ∈ Icc (-1 : ℝ) 1 := by
    intro u hu
    have h1 := Real.neg_one_le_cos (θ + φ); have h2 := Real.cos_le_one (θ + φ)
    have h3 := Real.neg_one_le_cos (θ - φ); have h4 := Real.cos_le_one (θ - φ)
    have hu1 : 0 ≤ 1 - u := by linarith [hu.2]
    constructor <;> nlinarith [hu.1]
  set W : ℝ → ℂ := fun u => exp ((Real.arccos (xr u) : ℂ) * I)
  have hW1 : ∀ u, ‖W u‖ = 1 := fun u => norm_exp_ofReal_mul_I _
  have hW0 : ∀ u, W u ≠ 0 := fun u => exp_ne_zero _
  have hWx : ∀ u ∈ Icc (0 : ℝ) 1, (W u + (W u)⁻¹) / 2 = (xr u : ℂ) := by
    intro u hu
    rw [exp_add_inv_div_two, ← ofReal_cos, Real.cos_arccos (hxr u hu).1 (hxr u hu).2]
  have hxc : ∀ u : ℝ, (xr u : ℂ) = (u : ℂ) * cos ((θ : ℂ) + φ) + (1 - u : ℂ) * cos ((θ : ℂ) - φ) :=
    fun u => by simp only [xr]; push_cast; ring
  -- the Euler weight
  set g : ℝ → ℂ := fun u => (u : ℂ) ^ (ν - 1) * (1 - u : ℂ) ^ (ν - 1)
  have hg : IntegrableOn g (Ioo 0 1) := by
    simpa [g] using integrableOn_eulerKernel_mul hν hν (f := fun _ => (1 : ℂ)) continuousOn_const
  set Gm : ℕ → ℝ → ℂ := fun m u => (gegenbauer ν m).eval (xr u : ℂ)
  have hGc : ∀ m, Continuous (Gm m) := fun m => by
    simp only [Gm, xr]
    exact (Polynomial.continuous _).comp (by fun_prop)
  set a : ℕ → ℂ := fun m => m.factorial * (gegenbauer ν m).eval (cos θ) *
    (gegenbauer ν m).eval (cos φ) * (Gamma (2 * ν + m))⁻¹
  set b : ℕ → ℂ := fun m => (Gamma ν * Gamma ν)⁻¹ * ∫ u in Ioo (0 : ℝ) 1, g u * Gm m u
  set F : ℂ → ℂ := fun t => regCarlsonR (-ν) (pair ν ν)
    (pair (1 - 2 * t * cos ((θ : ℂ) + φ) + t ^ 2) (1 - 2 * t * cos ((θ : ℂ) - φ) + t ^ 2))
  have hδ : (0 : ℝ) < 1 / 4 := by norm_num
  have hA : ∀ t : ℂ, ‖t‖ < 1 / 4 → HasSum (fun m => a m * t ^ m) (F t) := by
    intro t ht
    refine (hasSum_regOssicini hν θ φ (by linarith)).congr_fun fun m => ?_
    simp only [a]; ring
  have hB : ∀ t : ℂ, ‖t‖ < 1 / 4 → HasSum (fun m => b m * t ^ m) (F t) := by
    intro t ht
    have hcosθφ : ∀ s : ℝ, ‖cos (s : ℂ)‖ ≤ 1 := fun s => by
      rw [← ofReal_cos, Complex.norm_real, Real.norm_eq_abs]; exact Real.abs_cos_le_one s
    have hnode : ∀ s : ℝ, 0 < (1 - 2 * t * cos (s : ℂ) + t ^ 2).re := by
      intro s
      have hv : ‖2 * t * cos (s : ℂ) - t ^ 2‖ < 1 := by
        calc ‖2 * t * cos (s : ℂ) - t ^ 2‖ ≤ ‖2 * t * cos (s : ℂ)‖ + ‖t ^ 2‖ := norm_sub_le _ _
          _ ≤ 2 * ‖t‖ * 1 + ‖t‖ ^ 2 := by
              rw [norm_mul, norm_mul, norm_pow, Complex.norm_ofNat]
              gcongr; exact hcosθφ s
          _ < 1 := by nlinarith [norm_nonneg t]
      have := re_one_sub_pos hv
      rw [show 1 - (2 * t * cos (s : ℂ) - t ^ 2) = 1 - 2 * t * cos (s : ℂ) + t ^ 2 by ring] at this
      exact this
    have hdom : pair (1 - 2 * t * cos ((θ : ℂ) + φ) + t ^ 2)
        (1 - 2 * t * cos ((θ : ℂ) - φ) + t ^ 2) ∈ carlsonRVariableDomain := by
      intro i; fin_cases i
      · simpa [carlsonRightHalfPlane] using hnode (θ + φ)
      · simpa [carlsonRightHalfPlane] using hnode (θ - φ)
    have hbc : pair ν ν ∈ mvBetaConvergent := fun i => by fin_cases i <;> simpa
    have hF : F t = (Gamma ν * Gamma ν)⁻¹ * ∫ u in Ioo (0 : ℝ) 1,
        g u * (1 - 2 * t * (xr u : ℂ) + t ^ 2) ^ (-ν) := by
      simp only [F]
      rw [regCarlsonR_eq_regCarlsonRIntegral _ hbc hdom, regCarlsonRIntegral,
        regCarlsonDirichletAverage_pair_eq, regEulerIntegral]
      congr 2
      funext u
      simp only [g]
      rw [hxc u]
      ring_nf
    -- termwise
    set Fm : ℕ → ℝ → ℂ := fun m u => g u * (Gm m u * t ^ m)
    have hFint : ∀ m, Integrable (Fm m) (volume.restrict (Ioo 0 1)) := by
      intro m
      refine (integrableOn_eulerKernel_mul hν hν (f := fun u => Gm m u * t ^ m)
        ((hGc m).mul continuous_const).continuousOn).congr_fun (fun u _ => ?_) measurableSet_Ioo
      simp only [Fm, g, mul_assoc]
    have hbound : ∀ m, ∀ u ∈ Icc (0 : ℝ) 1, ‖Gm m u‖ ≤
        (ascPochhammer ℝ m).eval (2 * ‖ν‖) / m.factorial := by
      intro m u hu
      have := norm_eval_gegenbauer_le ν (W u) (hW1 u) m
      rwa [hWx u hu] at this
    have hFnorm : ∀ m, ∫ u in Ioo (0 : ℝ) 1, ‖Fm m u‖ ≤ (∫ u in Ioo (0 : ℝ) 1, ‖g u‖) *
        ((ascPochhammer ℝ m).eval (2 * ‖ν‖) / m.factorial * ‖t‖ ^ m) := by
      intro m
      rw [← integral_mul_const]
      refine setIntegral_mono_on (hFint m).norm (hg.norm.mul_const _) measurableSet_Ioo
        fun u hu => ?_
      simp only [Fm, norm_mul, norm_pow]
      gcongr
      exact hbound m u (Ioo_subset_Icc_self hu)
    have hsumm : Summable fun m => ∫ u in Ioo (0 : ℝ) 1, ‖Fm m u‖ :=
      Summable.of_nonneg_of_le (fun m => integral_nonneg fun _ => norm_nonneg _) hFnorm
        ((summable_ascPochhammer_real_mul_pow_div_factorial _ (norm_nonneg t)
          (by linarith)).mul_left _)
    have hmain := hasSum_integral_of_summable_integral_norm hFint hsumm
    have htsum : ∀ u ∈ Ioo (0 : ℝ) 1, ∑' m, Fm m u =
        g u * (1 - 2 * t * (xr u : ℂ) + t ^ 2) ^ (-ν) := by
      intro u hu
      have hu' := Ioo_subset_Icc_self hu
      have hn1 : ‖t * W u‖ < 1 := by rw [norm_mul, hW1]; linarith
      have hn2 : ‖t * (W u)⁻¹‖ < 1 := by rw [norm_mul, norm_inv, hW1, inv_one]; linarith
      have hs := hasSum_gegenbauer_mul_pow ν (W u) t (hW0 u) hn1 hn2
      rw [hWx u hu'] at hs
      have hfac := one_sub_mul_exp_mul t (Real.arccos (xr u) : ℂ)
      rw [← ofReal_cos, Real.cos_arccos (hxr u hu').1 (hxr u hu').2] at hfac
      rw [← hfac, mul_cpow_of_re_pos (re_one_sub_pos hn1) (re_one_sub_pos hn2)]
      exact (hs.mul_left (g u)).tsum_eq
    rw [setIntegral_congr_fun measurableSet_Ioo htsum] at hmain
    rw [hF]
    refine (hmain.mul_left (Gamma ν * Gamma ν)⁻¹).congr_fun fun m => ?_
    simp only [b, Fm]
    rw [mul_assoc, ← integral_mul_const]
    congr 2; funext u; ring
  have hab := congrFun (coeff_eq_of_hasSum_pow hδ hA hB) n
  simp only [a, b] at hab
  -- conclude
  have h2ν : 0 < (2 * ν).re := by simp; linarith
  have hΓ2 := Gamma_ne_zero_of_re_pos h2ν
  have hΓn : Gamma (2 * ν + n) = (ascPochhammer ℂ n).eval (2 * ν) * Gamma (2 * ν) :=
    Gamma_add_nat_eq_ascPochhammer_mul h2ν n
  have hP : (ascPochhammer ℂ n).eval (2 * ν) ≠ 0 :=
    ascPochhammer_eval_ne_zero_of_re_pos (by simpa using h2ν) n
  have hfac : (n.factorial : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
  rw [carlsonDirichletAverage, sum_pair, ← two_mul, regCarlsonDirichletAverage_pair_eq,
    regEulerIntegral, eval_gegenbauer_one]
  have hint : (∫ u in Ioo (0 : ℝ) 1, (u : ℂ) ^ (ν - 1) * (1 - u : ℂ) ^ (ν - 1) *
      (gegenbauer ν n).eval ((u : ℂ) * cos ((θ : ℂ) + φ) + (1 - u : ℂ) * cos ((θ : ℂ) - φ))) =
      ∫ u in Ioo (0 : ℝ) 1, g u * Gm n u := by
    congr 1; funext u; simp only [g, Gm, hxc u]
  rw [hint]
  rw [hΓn] at hab
  field_simp at hab ⊢
  linear_combination hab

end Carlson.TwoVariable
