/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.HermiteSecondKind
public import Carlson.R.IntegerParameters

/-!
# The Chebyshev function of the second kind

Carlson's Lemma 7.4-1 evaluates the Jacobi function of the second kind for `α = β = -1/2` in
closed form: on the set `W = {(x, y) : |ph x - ph y| < π/2}`,
`R_{-n-1}(1/2 + n, 1/2 + n; x², y²) = (x y)⁻¹ ((x + y)/2)^{-2n}`.

The set `W` is written here as `re (x ȳ) > 0`. On `W` the segment `[x², y²]` avoids the origin,
so the left side is holomorphic in `(x, y)`; the set is open and connected, and near `(1, 1)`
the identity follows from the second quadratic transformation (6.9-8) and the elementary
evaluation (5.9-22) of `R_{-n-1}(n, 1; ·, ·)`. The identity theorem extends it to all of `W`.

## Main definitions

* `Carlson.chebyshevDomain`: Carlson's set `W`.

## Main results

* `Carlson.analyticOnNhd_regCarlsonDirichletAverage_sq_zpow`: holomorphy on `W`.
* `Carlson.regCarlsonDirichletAverage_chebyshev`: Lemma 7.4-1.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.4.
-/

open Complex MeasureTheory Filter Set Dirichlet
open scoped Topology Real ComplexConjugate
@[expose] public noncomputable section
namespace Carlson

/-- Carlson's set `W` of Section 7.4: the phases of `x` and `y` differ by less than `π/2`,
expressed as `re (x ȳ) > 0`. -/
def chebyshevDomain : Set (ℂ × ℂ) := {p | 0 < (p.1 * conj p.2).re}

/-- On `W` the segment from `x²` to `y²` avoids the origin. -/
theorem sq_segment_ne_zero {x y : ℂ} (h : 0 < (x * conj y).re) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (t : ℂ) * x ^ 2 + (1 - t) * y ^ 2 ≠ 0 := by
  have hx : x ≠ 0 := fun hx => by simp [hx] at h
  have hy : y ≠ 0 := fun hy => by simp [hy] at h
  intro h0
  have key : ((t : ℂ) * x ^ 2 + (1 - t) * y ^ 2) * conj (x * y) =
      ((t * normSq x : ℝ) : ℂ) * (x * conj y) +
        (((1 - t) * normSq y : ℝ) : ℂ) * conj (x * conj y) := by
    simp only [map_mul, Complex.conj_conj]
    push_cast
    rw [← mul_conj, ← mul_conj]; ring
  have hre := congrArg re key
  rw [h0, zero_mul, zero_re, add_re, re_ofReal_mul, re_ofReal_mul, conj_re] at hre
  have h1 : 0 ≤ t * normSq x := mul_nonneg ht.1 (normSq_nonneg _)
  have h2 : 0 ≤ (1 - t) * normSq y := mul_nonneg (by linarith [ht.2]) (normSq_nonneg _)
  have h3 : 0 < t * normSq x + (1 - t) * normSq y := by
    rcases eq_or_lt_of_le ht.1 with h | h
    · subst h; simp [normSq_pos.mpr hy]
    · have := mul_pos h (normSq_pos.mpr hx); linarith
  nlinarith

/-- `W` is open. -/
theorem isOpen_chebyshevDomain : IsOpen chebyshevDomain :=
  isOpen_lt continuous_const (by fun_prop)

/-- `W` is connected: it is the image of `(ℂ ∖ {0}) × {re w > 0}` under `(x, w) ↦ (x, x w)`. -/
theorem isPreconnected_chebyshevDomain : IsPreconnected chebyshevDomain := by
  have himg : chebyshevDomain = (fun q : ℂ × ℂ => (q.1, q.1 * conj q.2)) ''
      ({0}ᶜ ×ˢ {w : ℂ | 0 < w.re}) := by
    ext ⟨x, y⟩
    simp only [chebyshevDomain, mem_ofPred_eq, mem_image, mem_prod, mem_compl_iff,
      mem_singleton_iff, Prod.mk.injEq]
    constructor
    · intro h
      have hx : x ≠ 0 := fun hx => by simp [hx] at h
      refine ⟨(x, conj (y / x)), ⟨hx, ?_⟩, rfl, ?_⟩
      · have : (conj (y / x)).re = (x * conj y).re / normSq x := by
          rw [conj_re, div_re]
          simp only [mul_re, conj_re, conj_im]; ring
        rw [this]; exact div_pos h (normSq_pos.mpr hx)
      · rw [Complex.conj_conj]; field_simp
    · rintro ⟨⟨x', w⟩, ⟨hx', hw⟩, rfl, rfl⟩
      rw [map_mul, Complex.conj_conj, ← mul_assoc, mul_conj]
      rw [re_ofReal_mul]; exact mul_pos (normSq_pos.mpr hx') hw
  rw [himg]
  refine IsPreconnected.image ?_ _ (by fun_prop : Continuous fun q : ℂ × ℂ =>
    (q.1, q.1 * conj q.2)).continuousOn
  exact (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
    0).isPreconnected.prod (convex_halfSpace_re_gt 0).isPreconnected

/-- The integer-power average over the segment `[x², y²]` is holomorphic in `(x, y)` on `W`. -/
theorem analyticOnNhd_regCarlsonDirichletAverage_sq_zpow {a : ℂ} (ha : 0 < a.re) (m : ℤ) :
    AnalyticOnNhd ℂ (fun p : ℂ × ℂ => regCarlsonDirichletAverage (TwoVariable.pair a a)
      (TwoVariable.pair (p.1 ^ 2) (p.2 ^ 2)) (fun w => w ^ m)) chebyshevDomain := by
  have hfun : (fun p : ℂ × ℂ => regCarlsonDirichletAverage (TwoVariable.pair a a)
      (TwoVariable.pair (p.1 ^ 2) (p.2 ^ 2)) (fun w => w ^ m)) = fun p =>
      (Gamma a * Gamma a)⁻¹ * ∫ u in Icc (0 : ℝ) 1, (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a - 1) *
        ((u : ℂ) * p.1 ^ 2 + (1 - (u : ℂ)) * p.2 ^ 2) ^ m := by
    funext p
    rw [TwoVariable.regCarlsonDirichletAverage_pair_eq, Dirichlet.regEulerIntegral,
      integral_Icc_eq_integral_Ioo]
  rw [hfun]
  refine fun p hp => analyticAt_const.mul ?_
  have hg : IntegrableOn (fun u : ℝ => (u : ℂ) ^ (a - 1) * (1 - u : ℂ) ^ (a - 1)) (Icc 0 1) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    simpa using Dirichlet.integrableOn_eulerKernel_mul ha ha (f := fun _ => 1) continuousOn_const
  set Wk : Set ((ℂ × ℂ) × ℂ) := {q | q.2 * q.1.1 ^ 2 + (1 - q.2) * q.1.2 ^ 2 ≠ 0}
  have hWk : IsOpen Wk := isOpen_ne_fun (by fun_prop) continuous_const
  have hH : AnalyticOnNhd ℂ (fun q : (ℂ × ℂ) × ℂ => (q.2 * q.1.1 ^ 2 + (1 - q.2) * q.1.2 ^ 2) ^ m)
      Wk := by
    intro q hq
    have a0 : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.2) q := analyticAt_snd
    have a1 : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.1.1) q :=
      ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)).analyticAt q
    have a2 : AnalyticAt ℂ (fun q : (ℂ × ℂ) × ℂ => q.1.2) q :=
      ((ContinuousLinearMap.snd ℂ ℂ ℂ).comp (ContinuousLinearMap.fst ℂ (ℂ × ℂ) ℂ)).analyticAt q
    exact ((a0.mul (a1.pow 2)).add ((analyticAt_const.sub a0).mul (a2.pow 2))).zpow hq
  have h := analyticOnNhd_integral_mul_compact_kernel (μ := volume) isCompact_Icc hg
    (γ := fun u : ℝ => (u : ℂ)) continuous_ofReal.continuousOn isOpen_chebyshevDomain hH
    (fun q hq u hu => sq_segment_ne_zero hq hu)
  exact h p hp

/-- **Carlson's Lemma 7.4-1** (the Chebyshev function of the second kind): for `(x, y) ∈ W`,
`R_{-n-1}(1/2 + n, 1/2 + n; x², y²) = (x y)⁻¹ ((x + y)/2)^{-2n}`. Here `R_{-n-1}` is Carlson's
average of `w^{-n-1}`, written as `Γ(c)` times the regularized Dirichlet average. -/
theorem regCarlsonDirichletAverage_chebyshev (n : ℕ) {x y : ℂ} (h : 0 < (x * conj y).re) :
    Gamma ((1 / 2 + n) + (1 / 2 + n)) *
        regCarlsonDirichletAverage (TwoVariable.pair (1 / 2 + n) (1 / 2 + n))
          (TwoVariable.pair (x ^ 2) (y ^ 2)) (fun w => w ^ (-((n : ℤ) + 1))) =
      (x * y)⁻¹ * ((x + y) / 2) ^ (-(2 * n : ℤ)) := by
  set β : ℂ := 1 / 2 + n
  have hβ : 0 < β.re := by simp [β]; positivity
  have hL : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => Gamma (β + β) *
      regCarlsonDirichletAverage (TwoVariable.pair β β) (TwoVariable.pair (p.1 ^ 2) (p.2 ^ 2))
        (fun w => w ^ (-((n : ℤ) + 1)))) chebyshevDomain :=
    fun p hp => analyticAt_const.mul (analyticOnNhd_regCarlsonDirichletAverage_sq_zpow hβ _ p hp)
  have hR : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => (p.1 * p.2)⁻¹ * ((p.1 + p.2) / 2) ^ (-(2 * n : ℤ)))
      chebyshevDomain := by
    intro p hp
    have hx : p.1 ≠ 0 := fun hx => by simp [chebyshevDomain, hx] at hp
    have hy : p.2 ≠ 0 := fun hy => by simp [chebyshevDomain, hy] at hp
    have hs : (p.1 + p.2) / 2 ≠ 0 := by
      intro h0
      have : p.1 = -p.2 := by linear_combination 2 * h0
      simp only [chebyshevDomain, mem_ofPred_eq, this, neg_mul, mul_conj, neg_re, ofReal_re] at hp
      linarith [normSq_nonneg p.2]
    exact ((analyticAt_fst.mul analyticAt_snd).inv (mul_ne_zero hx hy)).mul
      (((analyticAt_fst.add analyticAt_snd).div_const).zpow hs)
  have h1 : ((1 : ℂ), (1 : ℂ)) ∈ chebyshevDomain := by simp [chebyshevDomain]
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_chebyshevDomain h1 (by
    -- near `(1, 1)` all the nodes lie in the right half-plane
    have c1 : Continuous fun q : ℂ × ℂ => q.1.re := by fun_prop
    have c2 : Continuous fun q : ℂ × ℂ => q.2.re := by fun_prop
    have c3 : Continuous fun q : ℂ × ℂ => (q.1 ^ 2).re := by fun_prop
    have c4 : Continuous fun q : ℂ × ℂ => (q.2 ^ 2).re := by fun_prop
    have c5 : Continuous fun q : ℂ × ℂ => (TwoVariable.arithmeticMeanSq q.1 q.2).re := by
      unfold TwoVariable.arithmeticMeanSq; fun_prop
    have c6 : Continuous fun q : ℂ × ℂ => (TwoVariable.geometricMeanSq q.1 q.2).re := by
      unfold TwoVariable.geometricMeanSq; fun_prop
    filter_upwards [c1.continuousAt.eventually_const_lt (show (0 : ℝ) < (1 : ℂ).re by norm_num),
      c2.continuousAt.eventually_const_lt (show (0 : ℝ) < (1 : ℂ).re by norm_num),
      c3.continuousAt.eventually_const_lt (show (0 : ℝ) < ((1 : ℂ) ^ 2).re by norm_num),
      c4.continuousAt.eventually_const_lt (show (0 : ℝ) < ((1 : ℂ) ^ 2).re by norm_num),
      c5.continuousAt.eventually_const_lt (show (0 : ℝ) <
        (TwoVariable.arithmeticMeanSq (1 : ℂ) 1).re by norm_num [TwoVariable.arithmeticMeanSq]),
      c6.continuousAt.eventually_const_lt (show (0 : ℝ) <
        (TwoVariable.geometricMeanSq (1 : ℂ) 1).re by norm_num [TwoVariable.geometricMeanSq])]
      with q hq1 hq2 hq3 hq4 hq5 hq6
    have hb : TwoVariable.pair β β ∈ Complex.mvBetaConvergent := by
      intro i; fin_cases i <;> exact hβ
    have hz : TwoVariable.pair (q.1 ^ 2) (q.2 ^ 2) ∈ carlsonRVariableDomain := by
      intro i; fin_cases i
      · exact hq3
      · exact hq4
    have hz' : TwoVariable.pair (TwoVariable.arithmeticMeanSq q.1 q.2)
        (TwoVariable.geometricMeanSq q.1 q.2) ∈ carlsonRVariableDomain := by
      intro i; fin_cases i
      · exact hq5
      · exact hq6
    have hR1 : regCarlsonDirichletAverage (TwoVariable.pair β β)
        (TwoVariable.pair (q.1 ^ 2) (q.2 ^ 2)) (fun w => w ^ (-((n : ℤ) + 1))) =
        regCarlsonR (-((n : ℂ) + 1)) (TwoVariable.pair β β)
          (TwoVariable.pair (q.1 ^ 2) (q.2 ^ 2)) := by
      rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz, regCarlsonRIntegral]
      congr 1; funext w
      rw [show (-((n : ℂ) + 1)) = ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring, cpow_intCast]
    rw [hR1, TwoVariable.regRSlit_secondQuadratic _ β _ _ hq1 hq2,
      show 2 * β + -((n : ℂ) + 1) = (n : ℂ) by simp only [β]; ring,
      show 1 / 2 - β - -((n : ℂ) + 1) = 1 by simp only [β]; ring]
    have hsum : ∑ i, TwoVariable.pair (n : ℂ) 1 i = n + 1 := TwoVariable.sum_pair _ _
    have hneg := regCarlsonR_neg_sum_sub_nat 0 (TwoVariable.pair (n : ℂ) 1) hz'
    rw [hsum, Nat.cast_zero, sub_zero, regCarlsonRPolynomial_zero, hsum] at hneg
    rw [hneg, ← mul_assoc, ← mul_assoc, TwoVariable.Gamma_mul_quadraticGammaRatio hβ,
      show β + 1 / 2 = (n : ℂ) + 1 by simp only [β]; ring]
    have hΓ : Gamma ((n : ℂ) + 1) ≠ 0 := by
      rw [Complex.Gamma_nat_eq_factorial]; exact_mod_cast n.factorial_ne_zero
    simp only [Fin.prod_univ_two, TwoVariable.pair, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one]
    rw [show (-(n : ℂ)) = (((-(n : ℤ)) : ℤ) : ℂ) by push_cast; ring, cpow_intCast,
      show (-(1 : ℂ)) = (((-1 : ℤ)) : ℂ) by push_cast; ring, cpow_intCast]
    simp only [TwoVariable.arithmeticMeanSq, TwoVariable.geometricMeanSq]
    rw [← zpow_natCast ((q.1 + q.2) / 2) 2, ← zpow_mul, zpow_neg_one]
    field_simp
    ring_nf)
  have hxy := heq (show (x, y) ∈ chebyshevDomain from h)
  simp only at hxy
  exact hxy

end Carlson
