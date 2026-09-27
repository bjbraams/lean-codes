/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Hermite

/-!
# Weighted representation of Hermite coefficients

Carlson's Theorem 7.10-3: for a function `f` whose derivatives up to order `n` grow at
most like `e^{εx²}` with `ε < 1`,
`∫ f p̃ₙ e^{-x²} dx = 2⁻ⁿ ∫ f⁽ⁿ⁾ e^{-x²} dx`.
The proof integrates by parts `n` times using Rodrigues' formula (7.10-6).

## Main results

* `hermiteGaussianDeriv`: the derivatives `(-2)ʲ e^{-x²} p̃ⱼ(x)` of the Gaussian.
* `integral_mul_monicHermite_mul_exp`: Theorem 7.10-3.

## Implementation notes

Carlson assumes that `f` is holomorphic near the real line and that
`f⁽ᵐ⁾(x) e^{-εx²} → 0` for `m ≤ n - 1`. Here `f : ℝ → ℂ` only needs `n - 1`
differentiable derivatives, and the growth bound is also assumed for `f⁽ⁿ⁾`, so that
the right side is an absolutely convergent integral.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.10.
-/

@[expose] public noncomputable section

open Complex Set Filter Polynomial Finset MeasureTheory
open scoped Topology

namespace Carlson.TwoVariable

/-- The `j`-th derivative of the Gaussian, `(-2)ʲ e^{-x²} p̃ⱼ(x)`, on the real line. -/
def hermiteGaussianDeriv (j : ℕ) (x : ℝ) : ℂ :=
  (-2 : ℂ) ^ j * cexp (-(x : ℂ) ^ 2) * (monicHermite j).eval (x : ℂ)

/-- The real-variable Gaussian derivatives differentiate into each other. -/
theorem hasDerivAt_hermiteGaussianDeriv (j : ℕ) (x : ℝ) :
    HasDerivAt (hermiteGaussianDeriv j) (hermiteGaussianDeriv (j + 1) x) x :=
  (hasDerivAt_hermiteGaussian j (x : ℂ)).comp_ofReal

/-- Polynomials are integrable against every Gaussian `e^{-b x²}` with `b > 0`. -/
theorem integrable_eval_mul_exp_neg_mul_sq (p : ℂ[X]) {b : ℝ} (hb : 0 < b) :
    Integrable (fun x : ℝ => p.eval (x : ℂ) * ((Real.exp (-b * x ^ 2) : ℝ) : ℂ)) := by
  conv => arg 1; ext x; rw [p.as_sum_range_C_mul_X_pow]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sum_mul]
  refine integrable_finsetSum _ (fun k _ => ?_)
  have hk : Integrable (fun x : ℝ => ((x ^ k * Real.exp (-b * x ^ 2) : ℝ) : ℂ)) := by
    refine Integrable.ofReal ?_
    have h := integrable_rpow_mul_exp_neg_mul_sq (b := b) hb (s := (k : ℝ))
      (by linarith [Nat.cast_nonneg (α := ℝ) k])
    simp only [Real.rpow_natCast] at h
    exact h
  refine (hk.const_mul (p.coeff k)).congr (Eventually.of_forall fun x => ?_)
  push_cast
  ring

/-- Integrability of a function of Gaussian-dominated growth against a Gaussian derivative. -/
theorem integrable_mul_hermiteGaussianDeriv {g : ℝ → ℂ} (hg : AEStronglyMeasurable g volume)
    {ε C : ℝ} (hε : ε < 1) (hC : ∀ x, ‖g x‖ ≤ C * Real.exp (ε * x ^ 2)) (j : ℕ) :
    Integrable (fun x => g x * hermiteGaussianDeriv j x) := by
  have hb : 0 < 1 - ε := by linarith
  have hI := (integrable_eval_mul_exp_neg_mul_sq (monicHermite j) hb).norm.const_mul (C * 2 ^ j)
  have hc : Continuous (hermiteGaussianDeriv j) := by
    unfold hermiteGaussianDeriv; fun_prop
  refine hI.mono' (hg.mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun x => ?_)
  have hE : ‖hermiteGaussianDeriv j x‖ =
      2 ^ j * Real.exp (-x ^ 2) * ‖(monicHermite j).eval (x : ℂ)‖ := by
    simp only [hermiteGaussianDeriv, norm_mul, norm_pow, norm_neg, Complex.norm_ofNat]
    rw [show -(x : ℂ) ^ 2 = ((-x ^ 2 : ℝ) : ℂ) by push_cast; ring, norm_exp_ofReal]
  rw [norm_mul, hE, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hexp : Real.exp (ε * x ^ 2) * Real.exp (-x ^ 2) = Real.exp (-(1 - ε) * x ^ 2) := by
    rw [← Real.exp_add]; ring_nf
  calc ‖g x‖ * (2 ^ j * Real.exp (-x ^ 2) * ‖(monicHermite j).eval (x : ℂ)‖)
      ≤ C * Real.exp (ε * x ^ 2) * (2 ^ j * Real.exp (-x ^ 2) *
          ‖(monicHermite j).eval (x : ℂ)‖) := by gcongr; exact hC x
    _ = C * 2 ^ j * (‖(monicHermite j).eval (x : ℂ)‖ * Real.exp (-(1 - ε) * x ^ 2)) := by
      rw [← hexp]; ring

/-- **Theorem 7.10-3** (with Lebesgue measure in place of `dγ = π^{-1/2} e^{-x²} dx`):
`∫ f p̃ₙ e^{-x²} dx = 2⁻ⁿ ∫ f⁽ⁿ⁾ e^{-x²} dx` when `f, …, f⁽ⁿ⁾` grow at most like
`e^{εx²}` with `ε < 1`. -/
theorem integral_mul_monicHermite_mul_exp {f : ℝ → ℂ} {n : ℕ}
    (hf : ∀ m < n, Differentiable ℝ (iteratedDeriv m f)) {ε C : ℝ} (hε : ε < 1)
    (hC : ∀ m ≤ n, ∀ x, ‖iteratedDeriv m f x‖ ≤ C * Real.exp (ε * x ^ 2)) :
    ∫ x : ℝ, f x * (monicHermite n).eval (x : ℂ) * cexp (-(x : ℂ) ^ 2) =
      (2 : ℂ)⁻¹ ^ n * ∫ x : ℝ, iteratedDeriv n f x * cexp (-(x : ℂ) ^ 2) := by
  have hmeas : ∀ m ≤ n, 0 < n → AEStronglyMeasurable (iteratedDeriv m f) volume := by
    intro m hm hn
    rcases hm.lt_or_eq with hm | rfl
    · exact (hf m hm).continuous.aestronglyMeasurable
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hn
      rw [zero_add, iteratedDeriv_succ]
      exact (measurable_deriv _).aestronglyMeasurable
  have key : ∀ k ≤ n, ∫ x : ℝ, f x * hermiteGaussianDeriv n x =
      (-1 : ℂ) ^ k * ∫ x : ℝ, iteratedDeriv k f x * hermiteGaussianDeriv (n - k) x := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      have hkn : k < n := by omega
      have hI : ∀ m ≤ n, ∀ j, Integrable (fun x => iteratedDeriv m f x * hermiteGaussianDeriv j x) :=
        fun m hm j => integrable_mul_hermiteGaussianDeriv (hmeas m hm (by omega)) hε (hC m hm) j
      have hsplit : n - k = n - (k + 1) + 1 := by omega
      rw [ih (by omega), hsplit]
      have hibp := integral_mul_deriv_eq_deriv_mul_of_integrable
        (u := iteratedDeriv k f) (u' := iteratedDeriv (k + 1) f)
        (v := hermiteGaussianDeriv (n - (k + 1)))
        (v' := hermiteGaussianDeriv (n - (k + 1) + 1))
        (fun x _ => by
          rw [iteratedDeriv_succ]
          exact ((hf k hkn) x).hasDerivAt)
        (fun x _ => hasDerivAt_hermiteGaussianDeriv _ x)
        (hI k hkn.le _) (hI (k + 1) hk _) (hI k hkn.le _)
      rw [hibp, pow_succ]
      ring
  have h := key n le_rfl
  simp only [Nat.sub_self, hermiteGaussianDeriv, pow_zero, one_mul, monicHermite_zero, eval_one,
    mul_one] at h
  have h' : ∫ x : ℝ, f x * (monicHermite n).eval (x : ℂ) * cexp (-(x : ℂ) ^ 2) =
      ((-2 : ℂ) ^ n)⁻¹ * ∫ x : ℝ, f x * ((-2 : ℂ) ^ n * cexp (-(x : ℂ) ^ 2) *
        (monicHermite n).eval (x : ℂ)) := by
    rw [← integral_const_mul]
    congr 1; funext x
    field_simp
  rw [h', h, ← mul_assoc]
  congr 1
  rw [show (-2 : ℂ) = -1 * 2 by norm_num, mul_pow, mul_inv, inv_pow, mul_assoc, mul_comm,
    mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ (by norm_num)), mul_one]

end Carlson.TwoVariable
