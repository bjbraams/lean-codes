/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ComplexOrthogonality
public import Carlson.Jacobi.Endpoints
public import Carlson.Jacobi.SecondKind
public import Pochhammer.Estimates
public import TauCeti.Analysis.SpecialFunctions.Pow.Complex

/-!
# Orthogonality on a complex segment

Carlson's integrals `∫_r^s F(x) (x - r)^β (s - x)^α dx` over a complex segment use the phase
convention `ph(x - r) = ph(s - r) = ph(s - x)`. Parametrizing by `x = r + t (s - r)` reduces
them to the complex Jacobi weight on the unit interval. This transports Representation 7.8-2
and the orthogonality Theorem 7.8-3 to arbitrary distinct complex endpoints, for
`re α, re β > -1`.

## Main results

* `jacobiSegmentIntegral`: Carlson's weighted segment integral.
* `jacobiSegmentIntegral_eq`: reduction to the unit interval.
* `jacobiSegmentIntegral_mul_jacobiOn`: Representation 7.8-2.
* `jacobiSegmentIntegral_jacobiOn_mul_jacobiOn`: Theorem 7.8-3.

## References

* `TauCeti.Analysis.SpecialFunctions.Pow.Complex`: the Tau Ceti contributors'
  `TauCeti.ofReal_mul_cpow`, used to split powers of positive real multiples.
* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Representation 7.8-2 and Theorem 7.8-3.
-/

@[expose] public noncomputable section
open Complex Set Filter Polynomial MeasureTheory
open scoped Topology Interval

namespace Carlson.TwoVariable

/-- Carlson's weighted integral over the complex segment from `r` to `s`,
`∫_r^s F(x) (x - r)^β (s - x)^α dx`, with the phases of `x - r` and `s - x` equal to the phase
of `s - r`. It is parametrized by `x = r + t (s - r)`. -/
def jacobiSegmentIntegral (α β r s : ℂ) (F : ℂ → ℂ) : ℂ :=
  (s - r) * ∫ t in (0 : ℝ)..1,
    F (r + t * (s - r)) * ((t : ℂ) * (s - r)) ^ β * ((1 - t : ℝ) * (s - r)) ^ α

/-- The segment integral reduces to the complex Jacobi weight on the unit interval. -/
theorem jacobiSegmentIntegral_eq (α β : ℂ) {r s : ℂ} (hrs : r ≠ s) (F : ℂ → ℂ) :
    jacobiSegmentIntegral α β r s F = (s - r) ^ (α + β + 1) *
      ∫ y in (0 : ℝ)..1, complexJacobiWeight α β y * F ((r - s) * y + s) := by
  have hsr : s - r ≠ 0 := sub_ne_zero.mpr (Ne.symm hrs)
  unfold jacobiSegmentIntegral
  have hsub := intervalIntegral.integral_comp_sub_left
    (fun t : ℝ => F (r + t * (s - r)) * ((t : ℂ) * (s - r)) ^ β * ((1 - t : ℝ) * (s - r)) ^ α)
    (1 : ℝ) (a := 0) (b := 1)
  simp only [sub_zero, sub_self] at hsub
  rw [← hsub, cpow_add _ _ hsr, cpow_add _ _ hsr, cpow_one, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [(Set.countable_singleton (1 : ℝ)).ae_notMem volume] with y hy1 hy
  simp only [mem_singleton_iff] at hy1
  rw [uIoc_of_le zero_le_one] at hy
  have hy1' : y < 1 := lt_of_le_of_ne hy.2 hy1
  simp only [complexJacobiWeight]
  rw [TauCeti.ofReal_mul_cpow (by linarith) _, show ((1 - (1 - y) : ℝ) : ℂ) = (y : ℂ) by
    push_cast; ring, TauCeti.ofReal_mul_cpow hy.1.le _]
  push_cast
  rw [show r + (1 - (y : ℂ)) * (s - r) = (r - s) * y + s by ring]
  ring

/-- The Pochhammer normalization of the monic polynomials is nonzero when `re (α + β) > -2`,
in particular when both parameters have real part greater than `-1`. -/
theorem ascPochhammer_ne_zero_of_re_gt {α β : ℂ} (hαβ : -2 < (α + β).re) (n : ℕ) :
    (ascPochhammer ℂ n).eval (α + β + n + 1) ≠ 0 := by
  rcases n with _ | n
  · simp
  · apply ascPochhammer_eval_ne_zero_of_re_pos
    simp only [add_re, natCast_re, one_re, Nat.cast_add, Nat.cast_one] at hαβ ⊢
    have := Nat.cast_nonneg (α := ℝ) n
    linarith

/-- Carlson's Representation 7.8-2 at arbitrary distinct complex endpoints: for `f` holomorphic
on a neighborhood of the segment and `re α, re β > -1`,
`∫_r^s f(x) pₙ(x) (x-r)^β (s-x)^α dx = (s-r)^(α+β+1+2n) / (1+α+β+n)ₙ ·
  ∫₀¹ y^(α+n) (1-y)^(β+n) f⁽ⁿ⁾(y r + (1-y) s) dy`. -/
theorem jacobiSegmentIntegral_mul_jacobiOn {α β : ℂ} (hα : -1 < α.re) (hβ : -1 < β.re)
    {r s : ℂ} (hrs : r ≠ s) {U : Set ℂ} (hU : IsOpen U) (hseg : segment ℝ r s ⊆ U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    jacobiSegmentIntegral α β r s (fun x => f x * (jacobiOn α β r s n).eval x) =
      (s - r) ^ (α + β + 1) * (s - r) ^ (2 * n) / (ascPochhammer ℂ n).eval (α + β + n + 1) *
        ∫ y in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) y *
          iteratedDeriv n f ((r - s) * y + s) := by
  have hP := ascPochhammer_ne_zero_of_re_gt (α := α) (β := β) (by simp only [add_re]; linarith) n
  have hmem : ∀ y ∈ Icc (0 : ℝ) 1, (r - s) * (y : ℂ) + s ∈ U := fun y hy => hseg
    ⟨y, 1 - y, hy.1, by linarith [hy.2], by ring, by simp [real_smul]; ring⟩
  have han : AnalyticOnNhd ℂ f U := hf.analyticOnNhd hU
  have hanI (k : ℕ) : AnalyticOnNhd ℂ (iteratedDeriv k f) U := by
    simpa [iteratedDeriv_eq_iterate] using han.iterated_deriv k
  set g : ℕ → ℝ → ℂ := fun k y => (r - s) ^ k * iteratedDeriv k f ((r - s) * y + s)
  have hgc : ∀ k ≤ n, ContinuousOn (g k) (Icc 0 1) := by
    intro k _
    refine continuousOn_const.mul ?_
    exact (hanI k).continuousOn.comp
      ((continuous_const.mul continuous_ofReal).add continuous_const).continuousOn hmem
  have hgd : ∀ k < n, ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt (g k) (g (k + 1) y) y := by
    intro k _ y hy
    have hx := hmem y (Ioo_subset_Icc_self hy)
    have h1 : HasDerivAt (iteratedDeriv k f) (iteratedDeriv (k + 1) f ((r - s) * y + s))
        ((r - s) * y + s) := by
      rw [iteratedDeriv_succ]
      exact ((hanI k) _ hx).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun x : ℂ => iteratedDeriv k f ((r - s) * x + s))
        (iteratedDeriv (k + 1) f ((r - s) * y + s) * (r - s)) y := by
      have := h1.comp (y : ℂ) (((hasDerivAt_id (y : ℂ)).const_mul (r - s)).add_const s)
      simpa [Function.comp_def] using this
    have h3 := (h2.comp_ofReal).const_mul ((r - s) ^ k)
    convert h3 using 1
    simp only [g, pow_succ]; ring
  have hkey := factorial_mul_integral_complexJacobiWeight hα hβ n g hgc hgd
  rw [jacobiSegmentIntegral_eq α β hrs]
  have hpe (y : ℝ) : (jacobiOn α β r s n).eval ((r - s) * y + s) =
      (r - s) ^ n * ((n.factorial : ℂ) / ((-1 : ℂ) ^ n * (ascPochhammer ℂ n).eval
        (α + β + n + 1))) * (shiftedJacobi α β n).eval (y : ℂ) :=
    eval_jacobiOn_affine α β r s y n hP
  simp only [hpe]
  have hint : (∫ y in (0 : ℝ)..1, complexJacobiWeight α β y * (f ((r - s) * y + s) *
      ((r - s) ^ n * ((n.factorial : ℂ) / ((-1 : ℂ) ^ n *
        (ascPochhammer ℂ n).eval (α + β + n + 1))) * (shiftedJacobi α β n).eval (y : ℂ)))) =
      ((r - s) ^ n * ((n.factorial : ℂ) / ((-1 : ℂ) ^ n *
        (ascPochhammer ℂ n).eval (α + β + n + 1)))) *
      ∫ y in (0 : ℝ)..1,
        complexJacobiWeight α β y * g 0 y * (shiftedJacobi α β n).eval (y : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext y; simp only [g, pow_zero, one_mul, iteratedDeriv_zero]; ring
  rw [hint]
  have hg0 : (∫ y in (0 : ℝ)..1, complexJacobiWeight α β y * g 0 y *
      (shiftedJacobi α β n).eval (y : ℂ)) = (-1 : ℂ) ^ n / n.factorial *
      ((r - s) ^ n * ∫ y in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) y *
        iteratedDeriv n f ((r - s) * y + s)) := by
    have hf0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
    have hgn : (∫ y in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) y * g n y) =
        (r - s) ^ n * ∫ y in (0 : ℝ)..1, complexJacobiWeight (α + n) (β + n) y *
          iteratedDeriv n f ((r - s) * y + s) := by
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext y; simp only [g]; ring
    rw [hgn] at hkey
    field_simp
    linear_combination hkey
  rw [hg0]
  have hrs2 : (r - s) ^ n * (r - s) ^ n = (s - r) ^ (2 * n) := by
    rw [← pow_add, ← two_mul, show r - s = -(s - r) by ring, neg_pow, pow_mul, pow_mul]
    simp
  have hf0 : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hs0 : ((-1 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [← hrs2]
  field_simp

/-- The `n`-th derivative of a monic polynomial of degree `n` is the constant `n!`. -/
theorem iterate_derivative_of_monic {p : ℂ[X]} (hp : p.Monic) {n : ℕ} (hn : p.natDegree = n) :
    derivative^[n] p = C (n.factorial : ℂ) := by
  have hdeg : (derivative^[n] p).natDegree ≤ 0 :=
    (natDegree_iterate_derivative p n).trans (by omega)
  rw [eq_C_of_natDegree_le_zero hdeg, coeff_iterate_derivative, zero_add,
    Nat.descFactorial_self, ← hn, hp.coeff_natDegree, hn]
  simp

/-- Carlson's Theorem 7.8-3 at arbitrary distinct complex endpoints: the monic Jacobi polynomials
are orthogonal on the segment from `r` to `s` for `re α, re β > -1`, with squared norm
`Iₙ = n! B(1+α+n, 1+β+n) (s-r)^(1+α+β+2n) / (1+α+β+n)ₙ`. -/
theorem jacobiSegmentIntegral_jacobiOn_mul_jacobiOn {α β : ℂ} (hα : -1 < α.re)
    (hβ : -1 < β.re) {r s : ℂ} (hrs : r ≠ s) (m n : ℕ) :
    jacobiSegmentIntegral α β r s
        (fun x => (jacobiOn α β r s m).eval x * (jacobiOn α β r s n).eval x) =
      if m = n then (s - r) ^ (α + β + 1) * (s - r) ^ (2 * n) /
          (ascPochhammer ℂ n).eval (α + β + n + 1) * ((n.factorial : ℂ) *
            (Gamma (α + n + 1) * Gamma (β + n + 1) / Gamma (α + n + (β + n) + 2)))
        else 0 := by
  wlog hmn : m ≤ n generalizing m n
  · have h := this n m (le_of_not_ge hmn)
    rw [ite_eq_right (show ¬(n = m) by omega)] at h
    rw [ite_eq_right (show ¬(m = n) by omega)]
    rw [← h]
    unfold jacobiSegmentIntegral
    congr 2; funext t; ring
  have hrep := jacobiSegmentIntegral_mul_jacobiOn hα hβ hrs isOpen_univ (subset_univ _)
    ((jacobiOn α β r s m).differentiable.differentiableOn) n
  rw [hrep, iteratedDeriv_eval]
  have hP (m : ℕ) :=
    ascPochhammer_ne_zero_of_re_gt (α := α) (β := β) (by simp only [add_re]; linarith) m
  rcases lt_or_eq_of_le hmn with hlt | rfl
  · rw [ite_eq_right (show ¬(m = n) by omega)]
    have hdeg : (jacobiOn α β r s m).natDegree < n := by
      rw [natDegree_jacobiOn α β r s m (hP m)]
      exact hlt
    simp [iterate_derivative_eq_zero hdeg]
  · rw [ite_eq_left rfl, iterate_derivative_of_monic
      (monic_jacobiOn α β r s m (hP m))
      (natDegree_jacobiOn α β r s m (hP m))]
    simp only [eval_C]
    rw [show (fun y : ℝ => complexJacobiWeight (α + m) (β + m) y * (m.factorial : ℂ)) =
      fun y : ℝ => (m.factorial : ℂ) * complexJacobiWeight (α + m) (β + m) y by
        funext y; ring, intervalIntegral.integral_const_mul,
      integral_complexJacobiWeight (by simp; linarith) (by simp; linarith)]

end Carlson.TwoVariable
