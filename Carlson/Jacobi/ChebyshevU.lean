/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.ChebyshevSecondKind
public import Carlson.Jacobi.PolynomialSaddle
public import Carlson.Jacobi.FourierCosine
public import Carlson.Jacobi.Chebyshev
public import Carlson.TwoVariable.R.Elementary

/-!
# The Chebyshev cases of the second kind (Exercise 7.4-1)

For `α = β = 1/2` the monic Jacobi polynomials are `2⁻ⁿ Uₙ`; in the circle coordinate this gives
`Rₙ(-1/2 - n, -1/2 - n; x², y²) = (xy)⁻¹ [((x + y)/2)^{2n+2} - ((x - y)/2)^{2n+2}]`. The second
quadratic transformation reduces `R_{-n-1}(3/2 + n, 3/2 + n; x², y²)` to a single power on `W`.

## Main results

* `Carlson.TwoVariable.regCarlsonR_pair_zero_right`: a zero parameter, `R_t(c, 0; z) = z₀^t/Γ(c)`.
* `Carlson.TwoVariable.carlsonRPolynomial_chebyshevU`: Exercise 7.4-1, first formula.
* `Carlson.TwoVariable.regCarlsonDirichletAverage_chebyshevU`: Exercise 7.4-1, second formula.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §7.4.
-/

open Complex Polynomial Set Filter Dirichlet
open scoped Topology ComplexConjugate

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- **A zero parameter**: `R_t(c, 0; z) = z₀^t/Γ(c)` on the slit plane (regularized). -/
theorem regCarlsonR_pair_zero_right (t c : ℂ) {z : Fin 2 → ℂ} (hz : z ∈ carlsonRSlitDomain) :
    regCarlsonR t (pair c 0) z = z 0 ^ t * (Gamma c)⁻¹ := by
  set q : Option (Fin 1) → Fin 2 := fun o => Option.elim o 1 fun _ => 0
  have hq : Function.Surjective q := by
    intro k; fin_cases k
    · exact ⟨some 0, rfl⟩
    · exact ⟨none, rfl⟩
  set b' : Option (Fin 1) → ℂ := fun o => Option.elim o 0 fun _ => c
  have hagg : stdSimplexAggregate q b' = pair c 0 := by
    classical
    funext k
    rw [stdSimplexAggregate, FunOnFinite.linearMap_apply_apply]
    fin_cases k
    · have : (Finset.univ.filter fun o : Option (Fin 1) => q o = 0) = {some 0} := by decide
      show (Finset.univ.filter fun o => q o = 0).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
    · have : (Finset.univ.filter fun o : Option (Fin 1) => q o = 1) = {none} := by decide
      show (Finset.univ.filter fun o => q o = 1).sum _ = _
      rw [this, Finset.sum_singleton]; rfl
  have h := regCarlsonR_aggregate_of_slit hq t hz b'
  rw [hagg] at h
  rw [← h, regCarlsonR_option_zero t (b := b') (z := z ∘ q) rfl (fun o => hz (q o))]
  have hb : b' ∘ some = fun _ => c := rfl
  have hzq : (z ∘ q) ∘ some = fun _ => z 0 := rfl
  rw [hb, hzq, regCarlsonR_const_node t _ (hz 0)]
  simp

/-- **Exercise 7.4-1, second formula**: for `(x, y) ∈ W`,
`R_{-n-1}(3/2 + n, 3/2 + n; x², y²) = ((x + y)/2)^{-2n-2}`, with `R_{-n-1}` written as `Γ(c)` times
the regularized Dirichlet average of `w^{-n-1}`. -/
theorem regCarlsonDirichletAverage_chebyshevU (n : ℕ) {x y : ℂ} (h : 0 < (x * conj y).re) :
    Gamma ((3 / 2 + n) + (3 / 2 + n)) *
        regCarlsonDirichletAverage (pair (3 / 2 + n) (3 / 2 + n))
          (pair (x ^ 2) (y ^ 2)) (fun w => w ^ (-((n : ℤ) + 1))) =
      ((x + y) / 2) ^ (-(2 * n + 2 : ℤ)) := by
  set β : ℂ := 3 / 2 + n
  have hβ : 0 < β.re := by simp [β]; positivity
  have hL : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => Gamma (β + β) *
      regCarlsonDirichletAverage (pair β β) (pair (p.1 ^ 2) (p.2 ^ 2))
        (fun w => w ^ (-((n : ℤ) + 1)))) chebyshevDomain :=
    fun p hp => analyticAt_const.mul (analyticOnNhd_regCarlsonDirichletAverage_sq_zpow hβ _ p hp)
  have hR : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => ((p.1 + p.2) / 2) ^ (-(2 * n + 2 : ℤ)))
      chebyshevDomain := by
    intro p hp
    have hs : (p.1 + p.2) / 2 ≠ 0 := by
      intro h0
      have : p.1 = -p.2 := by linear_combination 2 * h0
      simp only [chebyshevDomain, mem_ofPred_eq, this, neg_mul, mul_conj, neg_re, ofReal_re] at hp
      linarith [normSq_nonneg p.2]
    exact ((analyticAt_fst.add analyticAt_snd).div_const).zpow hs
  have h1 : ((1 : ℂ), (1 : ℂ)) ∈ chebyshevDomain := by simp [chebyshevDomain]
  have heq := hL.eqOn_of_preconnected_of_eventuallyEq hR isPreconnected_chebyshevDomain h1 (by
    have c1 : Continuous fun q : ℂ × ℂ => q.1.re := by fun_prop
    have c2 : Continuous fun q : ℂ × ℂ => q.2.re := by fun_prop
    have c3 : Continuous fun q : ℂ × ℂ => (q.1 ^ 2).re := by fun_prop
    have c4 : Continuous fun q : ℂ × ℂ => (q.2 ^ 2).re := by fun_prop
    have c5 : Continuous fun q : ℂ × ℂ => (arithmeticMeanSq q.1 q.2).re := by
      unfold arithmeticMeanSq; fun_prop
    have c6 : Continuous fun q : ℂ × ℂ => (geometricMeanSq q.1 q.2).re := by
      unfold geometricMeanSq; fun_prop
    filter_upwards [c1.continuousAt.eventually_const_lt (show (0 : ℝ) < (1 : ℂ).re by norm_num),
      c2.continuousAt.eventually_const_lt (show (0 : ℝ) < (1 : ℂ).re by norm_num),
      c3.continuousAt.eventually_const_lt (show (0 : ℝ) < ((1 : ℂ) ^ 2).re by norm_num),
      c4.continuousAt.eventually_const_lt (show (0 : ℝ) < ((1 : ℂ) ^ 2).re by norm_num),
      c5.continuousAt.eventually_const_lt (show (0 : ℝ) <
        (arithmeticMeanSq (1 : ℂ) 1).re by norm_num [arithmeticMeanSq]),
      c6.continuousAt.eventually_const_lt (show (0 : ℝ) <
        (geometricMeanSq (1 : ℂ) 1).re by norm_num [geometricMeanSq])]
      with q hq1 hq2 hq3 hq4 hq5 hq6
    have hb : pair β β ∈ Complex.mvBetaConvergent := by
      intro i; fin_cases i <;> exact hβ
    have hz : pair (q.1 ^ 2) (q.2 ^ 2) ∈ carlsonRVariableDomain := by
      intro i; fin_cases i
      · exact hq3
      · exact hq4
    have hz' : pair (arithmeticMeanSq q.1 q.2) (geometricMeanSq q.1 q.2) ∈
        carlsonRSlitDomain := by
      intro i; fin_cases i
      · exact Or.inl hq5
      · exact Or.inl hq6
    have hR1 : regCarlsonDirichletAverage (pair β β) (pair (q.1 ^ 2) (q.2 ^ 2))
        (fun w => w ^ (-((n : ℤ) + 1))) =
        regCarlsonR (-((n : ℂ) + 1)) (pair β β) (pair (q.1 ^ 2) (q.2 ^ 2)) := by
      rw [regCarlsonR_eq_regCarlsonRIntegral _ hb hz, regCarlsonRIntegral]
      congr 1; funext w
      rw [show (-((n : ℂ) + 1)) = ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring, cpow_intCast]
    rw [hR1, regRSlit_secondQuadratic _ β _ _ hq1 hq2,
      show 2 * β + -((n : ℂ) + 1) = (n : ℂ) + 2 by simp only [β]; ring,
      show 1 / 2 - β - -((n : ℂ) + 1) = 0 by simp only [β]; ring,
      regCarlsonR_pair_zero_right _ _ hz', ← mul_assoc, Gamma_mul_quadraticGammaRatio hβ,
      show β + 1 / 2 = (n : ℂ) + 2 by simp only [β]; ring]
    have hΓ : Gamma ((n : ℂ) + 2) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
    simp only [pair, Matrix.cons_val_zero, arithmeticMeanSq]
    rw [show (-((n : ℂ) + 1)) = ((-((n : ℤ) + 1) : ℤ) : ℂ) by push_cast; ring, cpow_intCast,
      ← zpow_natCast ((q.1 + q.2) / 2) 2, ← zpow_mul]
    field_simp
    ring_nf)
  have hxy := heq (show (x, y) ∈ chebyshevDomain from h)
  simp only at hxy
  exact hxy

/-- The monic Jacobi polynomial with `α = β = 1/2` at `cos θ`:
`p̃ₙ(cos θ) sin θ = sin((n + 1)θ)/2ⁿ`. -/
theorem eval_monicJacobi_half_cos (n : ℕ) (θ : ℂ) :
    (monicJacobi (1 / 2 : ℂ) (1 / 2) n).eval (cos θ) * sin θ = sin ((n + 1) * θ) / 2 ^ n := by
  have hP : (ascPochhammer ℂ n).eval ((1 / 2 : ℂ) + 1 / 2 + n + 1) ≠ 0 := by
    apply ascPochhammer_eval_ne_zero_of_re_pos
    simp only [add_re, natCast_re, one_re, div_ofNat_re]; positivity
  have hmon := monic_monicJacobi (1 / 2 : ℂ) (1 / 2) n hP
  set c : ℂ := (2 ^ n * n.factorial : ℂ) / (ascPochhammer ℂ n).eval ((1 / 2 : ℂ) + 1 / 2 + n + 1) *
    ((ascPochhammer ℂ n).eval (3 / 2) / (n + 1).factorial)
  have he : monicJacobi (1 / 2 : ℂ) (1 / 2) n = C c * Chebyshev.U ℂ n := by
    rw [monicJacobi, jacobi_half_eq_chebyshev_U, ← mul_assoc, ← C_mul]
  have hlc : c * 2 ^ n = 1 := by
    have h1 := hmon.leadingCoeff
    rw [he, leadingCoeff_mul, leadingCoeff_C, Chebyshev.leadingCoeff_U_natCast] at h1
    exact h1
  rw [he, eval_mul, eval_C, mul_assoc, Chebyshev.U_complex_cos]
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [eq_div_iff h2]
  push_cast
  linear_combination sin ((n + 1) * θ) * hlc

/-- The `U`-type monic Jacobi polynomial in the circle coordinate:
`p̃ₙ((w + w⁻¹)/2) (w - w⁻¹) = (w^{n+1} - w^{-(n+1)})/2ⁿ`. -/
theorem eval_monicJacobi_half_laurent (n : ℕ) {w : ℂ} (hw : w ≠ 0) :
    (monicJacobi (1 / 2 : ℂ) (1 / 2) n).eval ((w + w⁻¹) / 2) * (w - w⁻¹) =
      (w ^ (n + 1) - (w⁻¹) ^ (n + 1)) / 2 ^ n := by
  set θ : ℂ := -(log w * I)
  have hθ : θ * I = log w := by simp only [θ]; rw [neg_mul, mul_assoc, I_mul_I]; ring
  have hc : cos θ = (w + w⁻¹) / 2 := by
    rw [Complex.cos, hθ, show -θ * I = -log w by rw [neg_mul, hθ], exp_neg, exp_log hw]
  have hs : sin θ = (w - w⁻¹) / (2 * I) := by
    rw [Complex.sin, hθ, show -θ * I = -log w by rw [neg_mul, hθ], exp_neg, exp_log hw]
    field_simp; rw [I_sq]; ring
  have hsn : sin ((n + 1) * θ) = (w ^ (n + 1) - (w⁻¹) ^ (n + 1)) / (2 * I) := by
    have h1 : ((n : ℂ) + 1) * θ * I = ((n + 1 : ℕ) : ℂ) * log w := by
      rw [mul_assoc, hθ]; push_cast; ring
    have h2 : -(((n : ℂ) + 1) * θ) * I = ((n + 1 : ℕ) : ℂ) * (-log w) := by
      rw [neg_mul, mul_assoc, hθ]; push_cast; ring
    rw [Complex.sin, h1, h2, exp_nat_mul, exp_nat_mul, exp_neg, exp_log hw]
    field_simp; rw [I_sq]; ring
  have h := eval_monicJacobi_half_cos n θ
  rw [hc, hs, hsn] at h
  have hI : (2 * I) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  generalize (monicJacobi (1 / 2 : ℂ) (1 / 2) n).eval ((w + w⁻¹) / 2) = M at h ⊢
  have h2 : (2 : ℂ) ^ n ≠ 0 := pow_ne_zero _ two_ne_zero
  rw [eq_div_iff h2]
  rw [mul_div_assoc', div_div, div_eq_div_iff hI (mul_ne_zero hI h2)] at h
  apply mul_left_cancel₀ hI
  linear_combination h

/-- **Exercise 7.4-1, first formula**, in numerator form: for `xy ≠ 0`,
`Rₙ(-1/2 - n, -1/2 - n; x², y²) = (xy)⁻¹ [((x + y)/2)^{2n+2} - ((x - y)/2)^{2n+2}]`, with
`Rₙ = Nₙ/(-1 - 2n)ₙ`. -/
theorem carlsonRPolynomial_chebyshevU (n : ℕ) {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    carlsonRPolynomialNumerator₂ n (-(1 / 2) - n) (-(1 / 2) - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (-(1 / 2) - 1 / 2 - 2 * (n : ℂ)) =
        (((x + y) / 2) ^ (2 * n + 2) - ((x - y) / 2) ^ (2 * n + 2)) / (x * y) := by
  have hc : (ascPochhammer ℂ n).eval (-(1 / 2) - 1 / 2 - 2 * (n : ℂ)) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, hk, h0⟩
    have := congrArg re h0
    simp at this
    have hk' : (k : ℝ) < n := by exact_mod_cast hk
    linarith
  by_cases hxy : x ^ 2 = y ^ 2
  · rw [← hxy, ← carlsonRPolynomialNumerator_pair]
    have hp : pair (x ^ 2) (x ^ 2) = fun _ => x ^ 2 := by funext i; fin_cases i <;> rfl
    rw [hp, carlsonRPolynomialNumerator_const, sum_pair,
      show -(1 / 2 : ℂ) - n + (-(1 / 2) - n) = -(1 / 2) - 1 / 2 - 2 * n by ring,
      mul_div_cancel_left₀ _ hc]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy with he | he
    · subst y
      rw [eq_div_iff (mul_ne_zero hx hx)]
      simp only [sub_self, zero_div, zero_pow (by omega : 2 * n + 2 ≠ 0), sub_zero]
      rw [show (x + x) / 2 = x by ring, pow_add, pow_mul]; ring
    · rw [eq_div_iff (mul_ne_zero hx hy), he]
      simp only [neg_add_cancel, zero_div, zero_pow (by omega : 2 * n + 2 ≠ 0), zero_sub]
      rw [show (-y - y) / 2 = -y by ring, pow_add, pow_mul]; ring
  have hm : x - y ≠ 0 := by intro h; exact hxy (congrArg (fun z : ℂ => z ^ 2) (sub_eq_zero.mp h))
  have hp : x + y ≠ 0 := by
    intro h
    have he : x = -y := eq_neg_of_add_eq_zero_left h
    rw [he, neg_sq] at hxy
    exact hxy rfl
  let d := (x ^ 2 - y ^ 2) / 2
  let w := (x + y) / (x - y)
  have hw : w ≠ 0 := div_ne_zero hp hm
  have hd : d ≠ 0 := by
    simp only [d]; intro h0; apply hxy; linear_combination 2 * h0
  have hplus : d * ((w + w⁻¹) / 2 + 1) = x ^ 2 := by
    dsimp [d, w]; field_simp; ring
  have hminus : d * ((w + w⁻¹) / 2 - 1) = y ^ 2 := by
    dsimp [d, w]; field_simp; ring
  have he : carlsonRPolynomialNumerator₂ n (-(1 / 2) - n) (-(1 / 2) - n) (x ^ 2) (y ^ 2) /
      (ascPochhammer ℂ n).eval (-(1 / 2) - 1 / 2 - 2 * (n : ℂ)) =
        d ^ n * (monicJacobi (1 / 2 : ℂ) (1 / 2) n).eval ((w + w⁻¹) / 2) := by
    rw [eval_monicJacobi_eq_numerator, ← mul_div_assoc, ← carlsonRPolynomialNumerator₂_mul,
      hplus, hminus]
  have hww : w - w⁻¹ = 2 * x * y / d := by dsimp [d, w]; field_simp; ring
  have hww0 : w - w⁻¹ ≠ 0 := by rw [hww]; exact div_ne_zero (by simp [hx, hy]) hd
  have hL := eval_monicJacobi_half_laurent n hw
  rw [he, eq_div_iff (mul_ne_zero hx hy)]
  have hA : d * w / 2 = ((x + y) / 2) ^ 2 := by dsimp [d, w]; field_simp; ring
  have hB : d * w⁻¹ / 2 = ((x - y) / 2) ^ 2 := by dsimp [d, w]; field_simp; ring
  rw [pow_add, pow_add, pow_mul, pow_mul, ← hA, ← hB]
  have hM : (monicJacobi (1 / 2 : ℂ) (1 / 2) n).eval ((w + w⁻¹) / 2) =
      (w ^ (n + 1) - (w⁻¹) ^ (n + 1)) / 2 ^ n / (w - w⁻¹) := by
    rw [eq_div_iff hww0]; exact hL
  rw [hM, hww]
  have hh : (1 / 2 : ℂ) ^ n * 2 ^ n = 1 := by rw [← mul_pow]; norm_num
  have hw1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
  clear_value d w
  have hwn : w ^ n * (w⁻¹) ^ n = 1 := by rw [← mul_pow, hw1, one_pow]
  rw [div_pow, mul_pow, div_pow, mul_pow, inv_pow]
  field_simp
  linear_combination w * hwn

end Carlson.TwoVariable
