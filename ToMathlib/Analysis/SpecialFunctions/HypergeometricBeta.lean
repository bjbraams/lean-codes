/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import ToMathlib.Analysis.SpecialFunctions.BetaSeries
public import ToMathlib.Analysis.SpecialFunctions.Bessel
public import ToMathlib.Algebra.Polynomial.PochhammerIdentities

/-!
# Hypergeometric parameter raising by beta integration

Carlson (1977), Exercise 4.4-4. The formula is stated for Mathlib's regularized
hypergeometric functions, so denominator parameters at nonpositive integers are
included. There is no restriction on the number of numerator or denominator
parameters: the argument belongs to the original series' convergence ball.
-/

open Polynomial Set MeasureTheory

public noncomputable section

namespace Complex

/-- The hypergeometric function is the totalized sum of its scalar power series. -/
theorem regularizedHGFun_eq_tsum (A C : Multiset ℂ) (z : ℂ) :
    regularizedHGFun A C z = ∑' n : ℕ, regularizedHGFunCoeff A C n * z ^ n := by
  rw [regularizedHGFun, regularizedHGFunSeries, ← FormalMultilinearSeries.ofScalarsSum,
    FormalMultilinearSeries.ofScalarsSum_eq_tsum]
  simp only [smul_eq_mul]

/-- Adjoining one numerator and one denominator parameter multiplies the coefficient
by a rising factorial and a reciprocal Gamma value. -/
theorem regularizedHGFunCoeff_cons_cons (A C : Multiset ℂ) (a c : ℂ) (n : ℕ) :
    regularizedHGFunCoeff (a ::ₘ A) (c ::ₘ C) n =
      regularizedHGFunCoeff A C n * (ascPochhammer ℂ n).eval a / Gamma (c + n) := by
  simp only [regularizedHGFunCoeff, Multiset.map_cons, Multiset.prod_cons,
    div_eq_mul_inv, mul_inv_rev]
  ring

/-- Scaling the argument by an interior beta variable preserves the original convergence ball. -/
private theorem mul_ofReal_mem_hypergeometric_ball {A C : Multiset ℂ} {z : ℂ}
    (hz : z ∈ Metric.eball 0 (regularizedHGFunSeries A C).radius)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    (u : ℂ) * z ∈ Metric.eball 0 (regularizedHGFunSeries A C).radius := by
  rw [Metric.mem_eball, edist_zero_right] at hz ⊢
  have hnorm : ‖(u : ℂ) * z‖ ≤ ‖z‖ := by
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hu.2.le
  apply lt_of_le_of_lt ?_ hz
  exact enorm_le_iff_norm_le.mpr hnorm

/-- A beta shift expressed as a rising factorial, with positive endpoint real parts. -/
private theorem betaIntegral_add_nat_left_eq {a b : ℂ} (ha : 0 < a.re) (hb : 0 < b.re)
    (n : ℕ) :
    betaIntegral (a + n) b = Gamma a * Gamma b *
      (ascPochhammer ℂ n).eval a / Gamma (a + b + n) := by
  have ha' : 0 < (a + n).re := by simp only [add_re, natCast_re]; positivity
  have hreg : ∀ k : ℕ, a ≠ -(k : ℂ) := by
    intro k hk
    have he := congrArg Complex.re hk
    simp only [neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hG : Gamma a ≠ 0 := Gamma_ne_zero_of_re_pos ha
  have he := (div_eq_iff hG).mp (Gamma_add_nat_div_Gamma_eq a hreg (n := n))
  rw [betaIntegral_eq_Gamma_mul_div _ _ ha' hb, he,
    show a + n + b = a + b + n by ring]
  ring

/-- **Carlson Exercise 4.4-4, first formula.** Beta integration adjoins one
numerator and one denominator parameter to any regularized hypergeometric series. -/
theorem integral_betaKernel_mul_regularizedHGFun {A C : Multiset ℂ} {a b z : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hz : z ∈ Metric.eball 0 (regularizedHGFunSeries A C).radius) :
    (Gamma a * Gamma b)⁻¹ *
        (∫ u : ℝ in Ioo 0 1, (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
          regularizedHGFun A C ((u : ℂ) * z)) =
      regularizedHGFun (a ::ₘ A) ((a + b) ::ₘ C) z := by
  let c : ℕ → ℂ := fun n => regularizedHGFunCoeff A C n * z ^ n
  have hc : Summable c := (hasSum_regularizedHGFun_of_mem_eball hz).summable
  have hs := hasSum_integral_betaKernel_mul ha hb hc
    (ψ := fun n u => (u : ℂ) ^ n) (fun n => by fun_prop)
    (fun n u hu => by
      rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hu.1]
      exact pow_le_one₀ hu.1.le hu.2.le)
    (f := fun u => regularizedHGFun A C ((u : ℂ) * z)) (fun u hu => by
      convert hasSum_regularizedHGFun_of_mem_eball
        (mul_ofReal_mem_hypergeometric_ball hz hu) using 1
      funext n
      dsimp [c]
      rw [mul_pow]
      ring)
  have ht := hs.mul_left (Gamma a * Gamma b)⁻¹
  have hterms : (fun n : ℕ => (Gamma a * Gamma b)⁻¹ *
      ∫ u : ℝ in Ioo 0 1, (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
        (c n * (u : ℂ) ^ n)) =
      fun n => regularizedHGFunCoeff (a ::ₘ A) ((a + b) ::ₘ C) n * z ^ n := by
    funext n
    have he := integral_betaKernel_mul_pow_mul_one_sub_pow a b (c n) n 0
    simp only [pow_zero, mul_one, Nat.cast_zero, add_zero] at he
    rw [he, betaIntegral_add_nat_left_eq ha hb, regularizedHGFunCoeff_cons_cons]
    dsimp [c]
    field_simp [Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hb]
  rw [hterms] at ht
  rw [regularizedHGFun_eq_tsum]
  exact ht.tsum_eq.symm

/-- Natural Gamma shifts in the right half-plane, from Mathlib's quotient identity. -/
private theorem Gamma_add_nat_of_pos {s : ℂ} (hs : 0 < s.re) (n : ℕ) :
    Gamma (s + n) = (ascPochhammer ℂ n).eval s * Gamma s := by
  apply (div_eq_iff (Gamma_ne_zero_of_re_pos hs)).mp
  exact Gamma_add_nat_div_Gamma_eq s (fun k hk => by
    have he := congrArg Complex.re hk
    simp only [neg_re, natCast_re] at he
    linarith [Nat.cast_nonneg (α := ℝ) k])

/-- The duplication identity for Gamma factors separated by an even natural shift. -/
private theorem Gamma_double_shift (s : ℂ) (hs : 0 < s.re) (n : ℕ) :
    Gamma (s + (2 * n : ℕ)) = (4 : ℂ) ^ n * Gamma s *
      Gamma (s / 2 + n) * Gamma ((s + 1) / 2 + n) /
        (Gamma (s / 2) * Gamma ((s + 1) / 2)) := by
  have h1 : 0 < (s / 2).re := by simp; linarith
  have h2 : 0 < ((s + 1) / 2).re := by simp; linarith
  have hd := ascPochhammer_eval_double (s / 2) n
  rw [show 2 * (s / 2) = s by ring,
    show s / 2 + 1 / 2 = (s + 1) / 2 by ring] at hd
  rw [Gamma_add_nat_of_pos hs, Gamma_add_nat_of_pos h1, Gamma_add_nat_of_pos h2, hd]
  field_simp [Gamma_ne_zero_of_re_pos h1, Gamma_ne_zero_of_re_pos h2]

/-- **Carlson Exercise 4.4-4, second formula.** The quadratic beta argument
adjoins two numerator and two half-sum denominator parameters. -/
theorem integral_betaKernel_mul_regularizedHGFun_quadratic {A C : Multiset ℂ} {a b z : ℂ}
    (ha : 0 < a.re) (hb : 0 < b.re)
    (hz : z ∈ Metric.eball 0 (regularizedHGFunSeries A C).radius) :
    (Gamma a * Gamma b)⁻¹ *
        (∫ u : ℝ in Ioo 0 1, (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
          regularizedHGFun A C ((u : ℂ) * (1 - (u : ℂ)) * z)) =
      (Gamma ((a + b) / 2) * Gamma ((a + b + 1) / 2) / Gamma (a + b)) *
        regularizedHGFun (a ::ₘ b ::ₘ A)
          (((a + b) / 2) ::ₘ ((a + b + 1) / 2) ::ₘ C) (z / 4) := by
  let c : ℕ → ℂ := fun n => regularizedHGFunCoeff A C n * z ^ n
  have hc : Summable c := (hasSum_regularizedHGFun_of_mem_eball hz).summable
  have hq (u : ℝ) (hu : u ∈ Ioo 0 1) : u * (1 - u) ∈ Ioo (0 : ℝ) 1 :=
    ⟨mul_pos hu.1 (sub_pos.mpr hu.2), by nlinarith [sq_nonneg (u - 1 / 2)]⟩
  have hs := hasSum_integral_betaKernel_mul ha hb hc
    (ψ := fun n u => (((u * (1 - u) : ℝ) : ℂ)) ^ n) (fun n => by fun_prop)
    (fun n u hu => by
      rw [norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos (hq u hu).1]
      exact pow_le_one₀ (hq u hu).1.le (hq u hu).2.le)
    (f := fun u => regularizedHGFun A C ((u : ℂ) * (1 - (u : ℂ)) * z)) (fun u hu => by
      convert hasSum_regularizedHGFun_of_mem_eball
        (mul_ofReal_mem_hypergeometric_ball hz (hq u hu)) using 1
      · funext n
        dsimp [c]
        rw [mul_pow]
        ring
      · push_cast; rfl)
  have ht := hs.mul_left (Gamma a * Gamma b)⁻¹
  have hab : 0 < (a + b).re := by simpa only [add_re] using add_pos ha hb
  have h1 : 0 < ((a + b) / 2).re := by simp; linarith
  have h2 : 0 < ((a + b + 1) / 2).re := by simp; linarith
  have hterms : (fun n : ℕ => (Gamma a * Gamma b)⁻¹ *
      ∫ u : ℝ in Ioo 0 1, (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
        (c n * (((u * (1 - u) : ℝ) : ℂ)) ^ n)) =
      fun n => (Gamma ((a + b) / 2) * Gamma ((a + b + 1) / 2) / Gamma (a + b)) *
        (regularizedHGFunCoeff (a ::ₘ b ::ₘ A)
          (((a + b) / 2) ::ₘ ((a + b + 1) / 2) ::ₘ C) n * (z / 4) ^ n) := by
    funext n
    have he := integral_betaKernel_mul_pow_mul_one_sub_pow a b (c n) n n
    have hrewrite : (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
        (c n * (((u * (1 - u) : ℝ) : ℂ)) ^ n)) =
        fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - (u : ℂ)) ^ (b - 1) *
          (c n * (u : ℂ) ^ n * (1 - (u : ℂ)) ^ n) := by
      funext u
      push_cast
      rw [mul_pow]
      ring
    rw [hrewrite, he, betaIntegral_eq_Gamma_mul_div _ _
      (by simp only [add_re, natCast_re]; positivity)
      (by simp only [add_re, natCast_re]; positivity),
      Gamma_add_nat_of_pos ha, Gamma_add_nat_of_pos hb,
      show a + n + (b + n) = a + b + (2 * n : ℕ) by push_cast; ring,
      Gamma_double_shift (a + b) hab]
    simp only [regularizedHGFunCoeff_cons_cons]
    dsimp [c]
    rw [div_pow]
    field_simp [Gamma_ne_zero_of_re_pos ha, Gamma_ne_zero_of_re_pos hb,
      Gamma_ne_zero_of_re_pos hab, Gamma_ne_zero_of_re_pos h1, Gamma_ne_zero_of_re_pos h2,
      Gamma_ne_zero_of_re_pos (show 0 < ((a + b) / 2 + n).re by
        simp only [add_re, natCast_re]; positivity),
      Gamma_ne_zero_of_re_pos (show 0 < ((a + b + 1) / 2 + n).re by
        simp only [add_re, natCast_re]; positivity)]
  rw [hterms] at ht
  rw [regularizedHGFun_eq_tsum]
  simpa only [tsum_mul_left] using ht.tsum_eq.symm

end Complex
