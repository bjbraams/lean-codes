/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.S
public import Carlson.TwoVariable.S
public import Carlson.TwoVariable.QuadraticContinuation
public import Carlson.TwoVariable.Quadratic.Polynomial
public import ComplexAnalysis.RealUniqueness

/-!
# The S-function with equal parameters

Carlson's Theorem 6.9-2: `S(β, β; x, y) = e^{(x+y)/2} ₀F₁[β + 1/2; (x-y)²/16]`. By the
exponential translation law it suffices to take opposite nodes; there the odd R-polynomials
vanish and the even ones are explicit (Theorem 6.9-1), and Legendre's duplication formula
turns the resulting coefficients into those of a `₀F₁` series.

The regularized form holds for every complex `β`: dividing by `Γ(2β)` gives the entire factor
`q(β) = 2^{1-2β} √π / Γ(β)` and the regularized `₀F₁` coefficients `1 / (n! Γ(β + 1/2 + n))`.

## Main results

* `Carlson.TwoVariable.evenCoeff_eq_quadraticGammaRatio`: the coefficient identity, entire in
  `β`.
* `Carlson.TwoVariable.hasSum_regCarlsonS_pair_self`: Theorem 6.9-2, regularized, for all `β`.
* `Carlson.TwoVariable.hasSum_carlsonS_pair_self`: Theorem 6.9-2 in Carlson's normalization,
  when `2β` is not a nonpositive integer.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Set Filter Polynomial
@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Natural shifts of Gamma in the right half-plane multiply by rising factorials. -/
private theorem Gamma_add_nat_eq_ascPochhammer_mul' {z : ℂ} (hz : 0 < z.re) (m : ℕ) :
    Gamma (z + m) = (ascPochhammer ℂ m).eval z * Gamma z := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hzm : z + m ≠ 0 := fun h => by
      have := congrArg re h; simp at this; linarith [Nat.cast_nonneg (α := ℝ) m]
    rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hzm, ih, ascPochhammer_succ_eval]
    ring

/-- The coefficient identity behind Theorem 6.9-2, entire in `β`:
`4ⁿ (β)ₙ (1/2)ₙ / ((2n)! Γ(2β + 2n)) = q(β) / (4ⁿ n! Γ(β + 1/2 + n))`, where
`q(β) = 2^{1-2β} √π / Γ(β)` is Legendre's duplication ratio. -/
theorem evenCoeff_eq_quadraticGammaRatio (β : ℂ) (n : ℕ) :
    (4 : ℂ) ^ n * (ascPochhammer ℂ n).eval β * (ascPochhammer ℂ n).eval (1 / 2) *
        (Gamma (2 * β + 2 * n))⁻¹ / ((2 * n).factorial : ℂ) =
      quadraticGammaRatio β / (4 ^ n * n.factorial * Gamma (β + 1 / 2 + n)) := by
  have hF : AnalyticOnNhd ℂ (fun β : ℂ => (4 : ℂ) ^ n * (ascPochhammer ℂ n).eval β *
      (ascPochhammer ℂ n).eval (1 / 2) * (Gamma (2 * β + 2 * n))⁻¹ /
        ((2 * n).factorial : ℂ)) univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    have h : Differentiable ℂ (fun β : ℂ => (Gamma (2 * β + 2 * n))⁻¹) := fun z =>
      (differentiable_one_div_Gamma _).comp z (by fun_prop)
    have hp : Differentiable ℂ (fun β : ℂ => (ascPochhammer ℂ n).eval β) :=
      Polynomial.differentiable _
    exact (by fun_prop : Differentiable ℂ _).differentiableOn
  have hG : AnalyticOnNhd ℂ (fun β : ℂ => quadraticGammaRatio β /
      (4 ^ n * n.factorial * Gamma (β + 1 / 2 + n))) univ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_univ
    have hq : Differentiable ℂ quadraticGammaRatio := fun z =>
      (analyticOnNhd_quadraticGammaRatio z trivial).differentiableAt
    have h : Differentiable ℂ (fun β : ℂ => (Gamma (β + (1 / 2 + n)))⁻¹) := fun z =>
      (differentiable_one_div_Gamma _).comp z (by fun_prop)
    have : (fun β : ℂ => quadraticGammaRatio β / (4 ^ n * n.factorial * Gamma (β + 1 / 2 + n))) =
        fun β => quadraticGammaRatio β * (4 ^ n * n.factorial : ℂ)⁻¹ *
          (Gamma (β + (1 / 2 + n)))⁻¹ := by
      funext β; rw [div_eq_mul_inv, mul_inv, add_assoc]; ring
    rw [this]
    exact ((hq.mul (differentiable_const _)).mul h).differentiableOn
  have h := hF.eq_of_eqOn_posReal hG fun b hb => by
    have hb' : 0 < ((b : ℂ)).re := by simpa using hb
    have hbn : 0 < ((b : ℂ) + n).re := by simp; positivity
    have hΓb := Gamma_ne_zero_of_re_pos hb'
    have hΓbn := Gamma_ne_zero_of_re_pos hbn
    have hΓh : Gamma ((b : ℂ) + 1 / 2 + n) ≠ 0 := Gamma_ne_zero_of_re_pos (by simp; positivity)
    have hdup := Complex.Gamma_mul_Gamma_add_half ((b : ℂ) + n)
    have hpoch := Gamma_add_nat_eq_ascPochhammer_mul' hb' n
    have hfac : ((2 * n).factorial : ℂ) = 4 ^ n * (ascPochhammer ℂ n).eval (1 / 2) *
        n.factorial := by
      have := ascPochhammer_eval_double (1 / 2 : ℂ) n
      rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, ascPochhammer_eval_one,
        show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num, ascPochhammer_eval_one] at this
      rw [this]
    have hhalf : (ascPochhammer ℂ n).eval (1 / 2 : ℂ) ≠ 0 :=
      ascPochhammer_eval_ne_zero_of_re_pos (by norm_num) n
    have h2 : (2 : ℂ) ^ (1 - 2 * ((b : ℂ) + n)) = 2 ^ (1 - 2 * (b : ℂ)) * ((4 : ℂ) ^ n)⁻¹ := by
      rw [show 1 - 2 * ((b : ℂ) + n) = (1 - 2 * (b : ℂ)) + -((2 * n : ℕ) : ℂ) by push_cast; ring,
        cpow_add _ _ two_ne_zero, cpow_neg, cpow_natCast, pow_mul]
      norm_num
    rw [show 2 * (b : ℂ) + 2 * n = 2 * ((b : ℂ) + n) by ring,
      show (b : ℂ) + 1 / 2 + n = (b : ℂ) + n + 1 / 2 by ring] at *
    have hΓ2 : Gamma (2 * ((b : ℂ) + n)) =
        Gamma ((b : ℂ) + n) * Gamma ((b : ℂ) + n + 1 / 2) /
          (2 ^ (1 - 2 * ((b : ℂ) + n)) * (Real.sqrt Real.pi : ℂ)) := by
      have hs : (2 : ℂ) ^ (1 - 2 * ((b : ℂ) + n)) * (Real.sqrt Real.pi : ℂ) ≠ 0 :=
        mul_ne_zero ((cpow_ne_zero_iff).mpr (Or.inl two_ne_zero))
          (by exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne')
      rw [eq_div_iff hs, hdup]; ring
    unfold quadraticGammaRatio
    rw [hΓ2, hfac, hpoch, h2]
    have hπ : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
      exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
    have hP : (ascPochhammer ℂ n).eval (b : ℂ) ≠ 0 :=
      ascPochhammer_eval_ne_zero_of_re_pos hb' n
    field_simp
  exact congrFun h β


/-- **Theorem 6.9-2** in regularized form, for all complex `β, x, y`:
`S(β, β; x, y) / Γ(2β) = q(β) e^{(x+y)/2} ∑ ((x-y)²/16)ⁿ / (n! Γ(β + 1/2 + n))`, where
`q(β) = Γ(β + 1/2) / Γ(2β)` in its entire form `2^{1-2β} √π / Γ(β)`. The series is Carlson's
`₀F₁[β + 1/2; (x-y)²/16]` with its denominator regularized. -/
theorem hasSum_regCarlsonS_pair_self (β x y : ℂ) :
    HasSum (fun n : ℕ => quadraticGammaRatio β * exp ((x + y) / 2) *
        (((x - y) ^ 2 / 16) ^ n / (n.factorial * Gamma (β + 1 / 2 + n))))
      (regCarlsonS (pair β β) (pair x y)) := by
  set w := (x - y) / 2
  set a := (x + y) / 2
  have hxy : pair x y = pair (w + a) (-w + a) := by
    congr 1 <;> simp only [w, a] <;> ring
  have hS : regCarlsonS (pair β β) (pair x y) = exp a * regSSeries β β w (-w) := by
    rw [hxy]; exact regSSeries_add_const β β w (-w) a
  have hser := hasSum_regCarlsonSSeries (pair w (-w)) (pair β β)
  -- only even terms survive
  have hodd : ∀ m ∉ Set.range (fun n : ℕ => 2 * n),
      (Nat.factorial m : ℂ)⁻¹ * regCarlsonRPolynomial m (pair β β) (pair w (-w)) = 0 := by
    intro m hm
    have hmo : Odd m := by
      rcases Nat.even_or_odd m with ⟨k, hk⟩ | h
      · exact absurd ⟨k, by show 2 * k = m; omega⟩ hm
      · exact h
    change _ * regRPolynomial m β β w (-w) = 0
    rw [regRPolynomial_eq_zero_of_odd m hmo, mul_zero]
  have heven := ((Function.Injective.hasSum_iff (fun a b h => by omega) hodd).mpr hser)
  rw [hS]
  have := heven.mul_left (exp a)
  refine this.congr_fun fun n => ?_
  simp only [Function.comp_apply]
  symm
  change exp a * ((Nat.factorial (2 * n) : ℂ)⁻¹ * regRPolynomial (2 * n) β β w (-w)) = _
  rw [regRPolynomial_eq_numerator₂_mul_one_div_Gamma, numerator₂_even_opposite]
  have hc := evenCoeff_eq_quadraticGammaRatio β n
  rw [show β + β + ((2 * n : ℕ) : ℂ) = 2 * β + 2 * n by push_cast; ring]
  have hw' : ((x - y) ^ 2 / 16) ^ n = w ^ (2 * n) / 4 ^ n := by
    rw [pow_mul, ← div_pow]; congr 1; simp only [w]; ring
  rw [hw']
  have h4 : ((4 : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  calc exp a * ((Nat.factorial (2 * n) : ℂ)⁻¹ * (4 ^ n * (ascPochhammer ℂ n).eval β *
          (ascPochhammer ℂ n).eval (1 / 2) * w ^ (2 * n) * (Gamma (2 * β + 2 * n))⁻¹))
      = exp a * w ^ (2 * n) * ((4 : ℂ) ^ n * (ascPochhammer ℂ n).eval β *
          (ascPochhammer ℂ n).eval (1 / 2) * (Gamma (2 * β + 2 * n))⁻¹ /
            ((2 * n).factorial : ℂ)) := by ring
    _ = _ := by
      rw [hc]
      field_simp

/-- **Theorem 6.9-2** in Carlson's form: if `2β` is not a nonpositive integer, then
`S(β, β; x, y) = e^{(x+y)/2} ₀F₁[β + 1/2; (x-y)²/16]`, with
`₀F₁[c; z] = ∑ zⁿ / ((c)ₙ n!)`. -/
theorem hasSum_carlsonS_pair_self {β : ℂ} (hβ : ∀ m : ℕ, 2 * β ≠ -m) (x y : ℂ) :
    HasSum (fun n : ℕ => exp ((x + y) / 2) *
        (((x - y) ^ 2 / 16) ^ n / ((ascPochhammer ℂ n).eval (β + 1 / 2) * n.factorial)))
      (carlsonS (pair β β) (pair x y)) := by
  have hΓ2 : Gamma (2 * β) ≠ 0 := Gamma_ne_zero hβ
  have hΓβ : Gamma β ≠ 0 := Gamma_ne_zero fun m h => hβ (2 * m) (by rw [h]; push_cast; ring)
  have hΓh : ∀ n : ℕ, Gamma (β + 1 / 2 + n) ≠ 0 := fun n => Gamma_ne_zero fun m h =>
    hβ (2 * (m + n) + 1) (by
      have : β = -(m : ℂ) - n - 1 / 2 := by linear_combination h
      rw [this]; push_cast; ring)
  have hdup := Complex.Gamma_mul_Gamma_add_half β
  have hq : Gamma (2 * β) * quadraticGammaRatio β = Gamma (β + 1 / 2) := by
    calc Gamma (2 * β) * quadraticGammaRatio β = (Gamma β * Gamma (β + 1 / 2)) * (Gamma β)⁻¹ := by
          rw [hdup]; unfold quadraticGammaRatio; ring
      _ = Gamma (β + 1 / 2) := by rw [mul_comm (Gamma β), mul_assoc, mul_inv_cancel₀ hΓβ, mul_one]
  unfold carlsonS
  rw [sum_pair, ← two_mul]
  refine ((hasSum_regCarlsonS_pair_self β x y).mul_left (Gamma (2 * β))).congr_fun fun n => ?_
  have hpoch : Gamma (β + 1 / 2 + n) = (ascPochhammer ℂ n).eval (β + 1 / 2) * Gamma (β + 1 / 2) := by
    induction n with
    | zero => simp
    | succ n ih =>
      have hne : β + 1 / 2 + n ≠ 0 := fun h0 => hΓh n (by rw [h0, Gamma_zero])
      rw [Nat.cast_succ, ← add_assoc, Gamma_add_one _ hne, ih, ascPochhammer_succ_eval]; ring
  have hΓh0 : Gamma (β + 1 / 2) ≠ 0 := by simpa using hΓh 0
  have hP : (ascPochhammer ℂ n).eval (β + 1 / 2) ≠ 0 := by
    intro h0; apply hΓh n; rw [hpoch, h0, zero_mul]
  rw [← mul_assoc, ← mul_assoc, hq, hpoch]
  have hΓh0' : Gamma ((2 * β + 1) / 2) ≠ 0 := by
    rw [show (2 * β + 1) / 2 = β + 1 / 2 by ring]; exact hΓh0
  have hP' : (ascPochhammer ℂ n).eval ((2 * β + 1) / 2) ≠ 0 := by
    rw [show (2 * β + 1) / 2 = β + 1 / 2 by ring]; exact hP
  field_simp

end Carlson.TwoVariable
