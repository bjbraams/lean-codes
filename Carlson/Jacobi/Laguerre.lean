/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EndpointBridge
public import Carlson.Jacobi.EndpointRodrigues
public import Pochhammer.Vandermonde
public import Pochhammer.Estimates

/-!
# Laguerre polynomials as limits of Jacobi polynomials

Carlson's monic Laguerre polynomial `p̃ₙ(x) = xⁿ ₂F₀(-n, -β-n; -1/x)` is the limit of the monic
Jacobi polynomial with endpoints `0, t` and first parameter `t` as `t → ∞` (Theorem 7.9-1).
Its moments against `x^β e^{-x}` are Gamma values times a rising factorial which, by the
Vandermonde identity, vanishes below the degree; this gives the orthogonality Theorem 7.9-4 for
complex `β` with `re β > -1`.

## Main results

* `monicLaguerre`: Carlson's monic Laguerre polynomial (Definition 7.9-2).
* `tendsto_eval_jacobiOn_monicLaguerre`: Theorem 7.9-1.
* `integral_pow_mul_monicLaguerre`: the moments.
* `integral_monicLaguerre_mul_monicLaguerre`: Theorem 7.9-4.
* `iteratedDeriv_cpow_mul_exp_neg`: the Rodrigues formula (7.9-8).

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.9.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial Finset MeasureTheory
open scoped Topology

namespace Carlson.TwoVariable

/-- Carlson's monic Laguerre polynomial `x^n ₂F₀(-n, -β-n; -1/x)`
(Definition 7.9-2), written as `Σₘ C(n,m) (-β-n)_{n-m} xᵐ`. -/
def monicLaguerre (β : ℂ) (n : ℕ) : ℂ[X] :=
  ∑ m ∈ range (n + 1), C ((n.choose m : ℂ) * (ascPochhammer ℂ (n - m)).eval (-β - n)) * X ^ m

/-- A shifted rising factorial grows like the corresponding power of `-t`. -/
theorem tendsto_ascPochhammer_sub_div_pow (a : ℂ) (k : ℕ) :
    Tendsto (fun t : ℝ => (ascPochhammer ℂ k).eval (a - t) / (-(t : ℂ)) ^ k) atTop (𝓝 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlin : Tendsto (fun t : ℝ => (a - t + k) / (-(t : ℂ))) atTop (𝓝 1) := by
      have h : Tendsto (fun t : ℝ => 1 - (a + k) * ((t : ℂ))⁻¹) atTop (𝓝 (1 - (a + k) * 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul
          ((continuous_ofReal.tendsto 0).comp tendsto_inv_atTop_zero |>.congr fun t => by simp))
      rw [mul_zero, sub_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with t ht
      have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
      field_simp
      ring
    have := ih.mul hlin
    rw [one_mul] at this
    refine this.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with t ht
    have ht' : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht.ne'
    rw [ascPochhammer_succ_eval, pow_succ]
    field_simp

/-- Carlson's Theorem 7.9-1: the monic Laguerre polynomial is the limit of monic Jacobi
polynomials on `[0, t]` with first parameter `t`, as `t → ∞`. -/
theorem tendsto_eval_jacobiOn_monicLaguerre (β x : ℂ) (n : ℕ) :
    Tendsto (fun t : ℝ => (jacobiOn (t : ℂ) β 0 t n).eval x) atTop
      (𝓝 ((monicLaguerre β n).eval x)) := by
  set A : ℕ → ℝ → ℂ := fun i t => (ascPochhammer ℂ i).eval ((-n : ℂ) - t) / (-(t : ℂ)) ^ i
  set B : ℕ → ℝ → ℂ := fun j t => (ascPochhammer ℂ 1).eval (x - t) / (-(t : ℂ)) ^ 1
  set D : ℝ → ℂ := fun t => (ascPochhammer ℂ n).eval ((-β - 2 * n : ℂ) - t) / (-(t : ℂ)) ^ n
  have hev : ∀ᶠ t : ℝ in atTop, (jacobiOn (t : ℂ) β 0 t n).eval x =
      ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℂ) * (ascPochhammer ℂ ij.2).eval (-β - n) *
        x ^ ij.1 * (A ij.1 t * B ij.2 t ^ ij.2 / D t) := by
    filter_upwards [eventually_gt_atTop (max 0 (-β.re - n - 1))] with t ht
    have ht0 : (0 : ℝ) < t := lt_of_le_of_lt (le_max_left _ _) ht
    have htC : (-(t : ℂ)) ≠ 0 := neg_ne_zero.mpr (ofReal_ne_zero.mpr ht0.ne')
    have hP : (ascPochhammer ℂ n).eval ((t : ℂ) + β + n + 1) ≠ 0 := by
      apply ascPochhammer_eval_ne_zero_of_re_pos
      simp only [add_re, ofReal_re, natCast_re, one_re]
      have := lt_of_le_of_lt (le_max_right _ _) ht
      linarith
    rw [eval_jacobiOn_eq_numerator _ _ _ _ _ _ hP, carlsonRPolynomialNumerator₂, sum_div]
    apply sum_congr rfl
    intro ij hij
    have hn : ij.1 + ij.2 = n := mem_antidiagonal.mp hij
    simp only [A, B, D, ascPochhammer_one, eval_X, pow_one]
    rw [show (-(t : ℂ) - n) = (-n : ℂ) - t by ring, sub_zero,
      show -(t : ℂ) - β - 2 * n = (-β - 2 * n : ℂ) - t by ring,
      show -β - (n : ℂ) = -β - n by ring]
    have hpow : (-(t : ℂ)) ^ n = (-(t : ℂ)) ^ ij.1 * (-(t : ℂ)) ^ ij.2 := by rw [← pow_add, hn]
    rw [div_pow, hpow]
    field_simp
  refine Tendsto.congr' (EventuallyEq.symm hev) ?_
  have hlim : Tendsto (fun t : ℝ => ∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℂ) *
      (ascPochhammer ℂ ij.2).eval (-β - n) * x ^ ij.1 * (A ij.1 t * B ij.2 t ^ ij.2 / D t))
      atTop (𝓝 (∑ ij ∈ antidiagonal n, (n.choose ij.1 : ℂ) *
        (ascPochhammer ℂ ij.2).eval (-β - n) * x ^ ij.1 * (1 * 1 ^ ij.2 / 1))) := by
    apply tendsto_finsetSum
    intro ij _
    exact tendsto_const_nhds.mul (((tendsto_ascPochhammer_sub_div_pow _ _).mul
      ((tendsto_ascPochhammer_sub_div_pow x 1).pow _)).div
        (tendsto_ascPochhammer_sub_div_pow _ _) one_ne_zero)
  convert hlim using 2
  simp only [one_pow, div_one, mul_one, monicLaguerre, eval_finsetSum, eval_mul, eval_C,
    eval_pow, eval_X]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- Natural shifts of Gamma in the right half-plane multiply by rising factorials. -/
theorem Gamma_add_nat_eq_ascPochhammer_mul {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    Gamma (z + m) = (ascPochhammer ℂ m).eval z * Gamma z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzm : z + m ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hzm, ih, ascPochhammer_succ_eval]
    ring

/-- The Laguerre weight `x^β e^{-x}` on the positive half-line has the Gamma function as its
moments. -/
theorem integral_pow_mul_laguerreWeight {β : ℂ} (hβ : -1 < β.re) (k : ℕ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ k * ((x : ℂ) ^ β * exp (-(x : ℂ))) = Gamma (β + k + 1) := by
  have hs : 0 < (β + k + 1).re := by
    simp only [add_re, natCast_re, one_re]; linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [Gamma_eq_integral hs, GammaIntegral]
  refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [ofReal_exp, ofReal_neg]
  rw [show β + k + 1 - 1 = β + k by ring, cpow_add _ _ hx0, cpow_natCast]
  ring

/-- Integrability of the monomial moments of the Laguerre weight. -/
theorem integrableOn_pow_mul_laguerreWeight {β : ℂ} (hβ : -1 < β.re) (k : ℕ) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ k * ((x : ℂ) ^ β * exp (-(x : ℂ)))) (Ioi 0) := by
  have hs : 0 < (β + k + 1).re := by
    simp only [add_re, natCast_re, one_re]; linarith [Nat.cast_nonneg (α := ℝ) k]
  refine (GammaIntegral_convergent hs).congr_fun (fun x hx => ?_) measurableSet_Ioi
  have hx0 : (x : ℂ) ≠ 0 := ofReal_ne_zero.mpr (ne_of_gt hx)
  simp only [ofReal_exp, ofReal_neg]
  rw [show β + k + 1 - 1 = β + k by ring, cpow_add _ _ hx0, cpow_natCast]
  ring

/-- Integrals of polynomials against the Laguerre weight are combinations of Gamma values. -/
theorem integral_eval_mul_laguerreWeight {β : ℂ} (hβ : -1 < β.re) (p : ℂ[X]) :
    ∫ x in Ioi (0 : ℝ), p.eval (x : ℂ) * ((x : ℂ) ^ β * exp (-(x : ℂ))) =
      ∑ k ∈ range (p.natDegree + 1), p.coeff k * Gamma (β + k + 1) := by
  conv_lhs => rw [p.as_sum_range_C_mul_X_pow]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sum_mul]
  rw [integral_finsetSum]
  · apply sum_congr rfl
    intro k _
    simp only [mul_assoc]
    rw [integral_const_mul, integral_pow_mul_laguerreWeight hβ]
  · intro k _
    simpa only [mul_assoc] using (integrableOn_pow_mul_laguerreWeight hβ k).const_mul (p.coeff k)

/-- The monic Laguerre polynomial is monic of degree `n`. -/
theorem coeff_monicLaguerre (β : ℂ) (n k : ℕ) :
    (monicLaguerre β n).coeff k =
      if k ≤ n then (n.choose k : ℂ) * (ascPochhammer ℂ (n - k)).eval (-β - n) else 0 := by
  simp only [monicLaguerre, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [sum_ite_eq]
  simp

/-- The degree of the monic Laguerre polynomial is at most `n`. -/
theorem natDegree_monicLaguerre_le (β : ℂ) (n : ℕ) : (monicLaguerre β n).natDegree ≤ n :=
  natDegree_le_iff_coeff_eq_zero.mpr fun k hk => by
    rw [coeff_monicLaguerre, ite_eq_right (not_le.mpr hk)]

/-- Moments of the monic Laguerre polynomials against the Laguerre weight: they vanish below the
degree, and equal `n! Γ(β+n+1)` at the degree. -/
theorem integral_pow_mul_monicLaguerre {β : ℂ} (hβ : -1 < β.re) (n k : ℕ) :
    ∫ x in Ioi (0 : ℝ), (x : ℂ) ^ k * ((monicLaguerre β n).eval (x : ℂ) *
        ((x : ℂ) ^ β * exp (-(x : ℂ)))) =
      Gamma (β + k + 1) * (ascPochhammer ℂ n).eval ((k : ℂ) + 1 - n) := by
  have hz : 0 < (β + k + 1).re := by
    simp only [add_re, natCast_re, one_re]; linarith [Nat.cast_nonneg (α := ℝ) k]
  have hterm (m : ℕ) : (fun x : ℝ => (x : ℂ) ^ k * ((C ((n.choose m : ℂ) *
      (ascPochhammer ℂ (n - m)).eval (-β - n)) * X ^ m).eval (x : ℂ) *
        ((x : ℂ) ^ β * exp (-(x : ℂ))))) = fun x : ℝ => ((n.choose m : ℂ) *
      (ascPochhammer ℂ (n - m)).eval (-β - n)) * ((x : ℂ) ^ (k + m) *
        ((x : ℂ) ^ β * exp (-(x : ℂ)))) := by
    funext x; simp only [eval_mul, eval_C, eval_pow, eval_X, pow_add]; ring
  simp only [monicLaguerre, eval_finsetSum, sum_mul, mul_sum]
  rw [integral_finsetSum _ (fun m _ => by
    rw [hterm m]; exact (integrableOn_pow_mul_laguerreWeight hβ (k + m)).const_mul _)]
  simp only [hterm, integral_const_mul, integral_pow_mul_laguerreWeight hβ]
  have hshift (m : ℕ) : Gamma (β + (k + m : ℕ) + 1) =
      (ascPochhammer ℂ m).eval (β + k + 1) * Gamma (β + k + 1) := by
    rw [← Gamma_add_nat_eq_ascPochhammer_mul hz m]; push_cast; ring_nf
  simp only [hshift]
  rw [show (k : ℂ) + 1 - n = (β + k + 1) + (-β - n) by ring,
    ascPochhammer_eval_add_sum_range, mul_sum]
  apply sum_congr rfl
  intro m _
  ring

/-- Polynomials are integrable against the Laguerre weight. -/
theorem integrableOn_eval_mul_laguerreWeight {β : ℂ} (hβ : -1 < β.re) (p : ℂ[X]) :
    IntegrableOn (fun x : ℝ => p.eval (x : ℂ) * ((x : ℂ) ^ β * exp (-(x : ℂ)))) (Ioi 0) := by
  conv => arg 1; ext x; rw [p.as_sum_range_C_mul_X_pow]
  simp only [eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X, sum_mul]
  refine integrable_finsetSum _ (fun k _ => ?_)
  simpa only [mul_assoc] using (integrableOn_pow_mul_laguerreWeight hβ k).const_mul (p.coeff k)

/-- Carlson's Theorem 7.9-4: the monic Laguerre polynomials are orthogonal on the positive
half-line with respect to `x^β e^{-x}` for `re β > -1`, with squared norm `n! Γ(β+n+1)`. -/
theorem integral_monicLaguerre_mul_monicLaguerre {β : ℂ} (hβ : -1 < β.re) (m n : ℕ) :
    ∫ x in Ioi (0 : ℝ), (monicLaguerre β m).eval (x : ℂ) * (monicLaguerre β n).eval (x : ℂ) *
        ((x : ℂ) ^ β * exp (-(x : ℂ))) =
      if m = n then (n.factorial : ℂ) * Gamma (β + n + 1) else 0 := by
  wlog hmn : m ≤ n generalizing m n
  · have h := this n m (le_of_not_ge hmn)
    rw [ite_eq_right (show ¬(n = m) by omega)] at h
    rw [ite_eq_right (show ¬(m = n) by omega), ← h]
    congr 1; funext x; ring
  have hterm (j : ℕ) : (fun x : ℝ => (C ((m.choose j : ℂ) *
      (ascPochhammer ℂ (m - j)).eval (-β - m)) * X ^ j).eval (x : ℂ) *
        (monicLaguerre β n).eval (x : ℂ) * ((x : ℂ) ^ β * exp (-(x : ℂ)))) =
      fun x : ℝ => ((m.choose j : ℂ) * (ascPochhammer ℂ (m - j)).eval (-β - m)) *
        ((x : ℂ) ^ j * ((monicLaguerre β n).eval (x : ℂ) * ((x : ℂ) ^ β * exp (-(x : ℂ))))) := by
    funext x; simp only [eval_mul, eval_C, eval_pow, eval_X]; ring
  conv_lhs => arg 2; ext x; rw [show (monicLaguerre β m).eval (x : ℂ) = ∑ j ∈ range (m + 1),
    (C ((m.choose j : ℂ) * (ascPochhammer ℂ (m - j)).eval (-β - m)) * X ^ j).eval (x : ℂ) by
      rw [monicLaguerre, eval_finsetSum]]
  simp only [sum_mul]
  rw [integral_finsetSum _ (fun j _ => by
    rw [hterm j]
    refine Integrable.const_mul ?_ _
    have h := integrableOn_eval_mul_laguerreWeight hβ (X ^ j * monicLaguerre β n)
    simp only [eval_mul, eval_pow, eval_X, mul_assoc] at h
    exact h)]
  simp only [hterm, integral_const_mul, integral_pow_mul_monicLaguerre hβ]
  have hzero (j : ℕ) (hj : j < n) : (ascPochhammer ℂ n).eval ((j : ℂ) + 1 - n) = 0 := by
    rw [show (j : ℂ) + 1 - n = -((n - 1 - j : ℕ) : ℂ) by
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; push_cast; ring]
    exact ascPochhammer_eval_neg_coe_nat_of_lt (by omega)
  rcases lt_or_eq_of_le hmn with hlt | rfl
  · rw [ite_eq_right (show ¬(m = n) by omega)]
    apply sum_eq_zero
    intro j hj
    rw [hzero j (by simp at hj; omega), mul_zero, mul_zero]
  · rw [ite_eq_left rfl, sum_range_succ, sum_eq_zero]
    · simp only [Nat.choose_self, Nat.cast_one, Nat.sub_self, ascPochhammer_zero, eval_one,
        mul_one, zero_add, show (m : ℂ) + 1 - m = 1 by ring, ascPochhammer_eval_one, one_mul]
      ring
    · intro j hj
      rw [hzero j (by simpa using hj), mul_zero, mul_zero]

/-- **Rodrigues' formula for Laguerre polynomials** (7.9-8), on the principal branch:
`Dⁿ[x^(β+n) e^{-x}] = (-1)ⁿ x^β e^{-x} p̃ₙ(x)`. -/
theorem iteratedDeriv_cpow_mul_exp_neg (β : ℂ) (n : ℕ) {x : ℂ} (hx : x ∈ slitPlane) :
    iteratedDeriv n (fun w => w ^ (β + n) * cexp (-w)) x =
      (-1 : ℂ) ^ n * (x ^ β * cexp (-x) * (monicLaguerre β n).eval x) := by
  have hx0 : x ≠ 0 := slitPlane_ne_zero hx
  have h1 : ContDiffAt ℂ n (fun w : ℂ => w ^ (β + n)) x := by
    simpa using contDiffAt_sub_cpow 0 (β + n) n (x := x) (by simpa using hx)
  have h2 : ContDiffAt ℂ n (fun w : ℂ => cexp (-w)) x :=
    (analyticAt_id.neg.cexp).contDiffAt
  have hexp : ∀ k : ℕ, iteratedDeriv k (fun w : ℂ => cexp (-w)) x = (-1) ^ k * cexp (-x) := by
    intro k
    have := iteratedDeriv_cexp_const_mul k (-1 : ℂ)
    simp only [neg_one_mul] at this
    rw [this]
  rw [iteratedDeriv_fun_mul h1 h2, monicLaguerre, eval_finsetSum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have hsub : n + 1 - 1 - i = n - i := by omega
  have hd := iteratedDeriv_sub_cpow 0 (β + n) (n - i) (x := x) (by simpa using hx)
  simp only [sub_zero] at hd
  rw [hsub, hd, hexp, Nat.sub_sub_self hin, Nat.choose_symm hin,
    show β + n - ((n - i : ℕ) : ℂ) = β + (i : ℂ) by push_cast [hin]; ring,
    cpow_add _ _ hx0, cpow_natCast, show -β - (n : ℂ) = -(β + n) by ring,
    ascPochhammer_eval_neg_eq_descPochhammer]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  have hsign : (-1 : ℂ) ^ (n - i) * (-1) ^ i = (-1) ^ n := by
    rw [← pow_add, Nat.sub_add_cancel hin]
  have hsq : (-1 : ℂ) ^ (n - i) * (-1) ^ (n - i) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  rw [← hsign]
  linear_combination (↑(n.choose i) * eval (β + ↑n) (descPochhammer ℂ (n - i)) * x ^ β * x ^ i *
    cexp (-x) * (-1) ^ i) * (-hsq)

end Carlson.TwoVariable
