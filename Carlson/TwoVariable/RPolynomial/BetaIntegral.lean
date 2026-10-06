/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.RPolynomial.SpecialValues
public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Carlson.RPolynomial.EqualParameterBounds
public import Pochhammer.Estimates

/-!
# A Beta-integral relation for equal-parameter R-polynomials (Exercise 6.9-7)

By (6.9-6), `Rₙ(β, β; x + y, x - y) = ∑ₘ (n choose 2m) (½)ₘ/(β + ½)ₘ x^(n-2m) y^{2m}`. Integrating
term by term against `u^{β - 1/2} (1 - u)^{σ - 1}` with `y` replaced by `y√u` raises the
parameter from `β` to `β + σ`, since `B(β + ½ + m, σ) = B(β + ½, σ) (β + ½)ₘ/(β + σ + ½)ₘ`.

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_add_sub_eq_mul`: (6.9-6) in Carlson's
  normalization.
* `Carlson.TwoVariable.integral_evenBinomialSum`: Exercise 6.9-7 for the sums of (6.9-6).
* `Carlson.TwoVariable.betaIntegral_mul_carlsonRPolynomial₂`: Exercise 6.9-7.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- Carlson's right side of (6.9-6), `∑ₘ (n choose 2m) (½)ₘ/(a)ₘ x^(n-2m) y^{2m}`, written as a
sum over all `j ≤ n` with the odd terms zero. With `a = β + ½` it is `Rₙ(β, β; x + y, x - y)`. -/
def evenBinomialSum (n : ℕ) (a x y : ℂ) : ℂ :=
  ∑ j ∈ range (n + 1), if Even j then (n.choose j : ℂ) * (ascPochhammer ℂ (j / 2)).eval (1 / 2) /
    (ascPochhammer ℂ (j / 2)).eval a * x ^ (n - j) * y ^ j else 0

/-- **Exercise 6.9-6**, Carlson's normalized form: if `(2β)ₙ ≠ 0`, then
`Rₙ(β, β; x + y, x - y) = ∑ₘ (n choose 2m) (½)ₘ/(β + ½)ₘ x^(n-2m) y^{2m}`. -/
theorem carlsonRPolynomialNumerator₂_add_sub_eq_mul (n : ℕ) (β x y : ℂ)
    (hβ : (ascPochhammer ℂ n).eval (2 * β) ≠ 0) :
    carlsonRPolynomialNumerator₂ n β β (x + y) (x - y) =
      (ascPochhammer ℂ n).eval (2 * β) * evenBinomialSum n (β + 1 / 2) x y := by
  rw [carlsonRPolynomialNumerator₂_add_sub, evenBinomialSum, mul_sum]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hj)
  split_ifs with he
  · obtain ⟨m, rfl⟩ := he
    rw [show m + m = 2 * m by ring] at hjn ⊢
    rw [Nat.mul_div_cancel_left m two_pos]
    have hsplit := ascPochhammer_eval_add (2 * β) (2 * m) (n - 2 * m)
    rw [Nat.add_sub_cancel' hjn, ascPochhammer_eval_double] at hsplit
    have hm : (ascPochhammer ℂ m).eval (β + 1 / 2) ≠ 0 := fun h0 => hβ (by
      rw [hsplit, h0]; ring)
    rw [hsplit]
    generalize (ascPochhammer ℂ m).eval (β + 1 / 2) = P at hm ⊢
    field_simp
  · simp

/-- The Beta integrals of the monomials: `B(a + m, σ) (a + σ)ₘ = B(a, σ) (a)ₘ`. -/
theorem betaIntegral_add_nat_mul {a σ : ℂ} (ha : 0 < a.re) (hσ : 0 < σ.re) (m : ℕ) :
    betaIntegral (a + m) σ * (ascPochhammer ℂ m).eval (a + σ) =
      betaIntegral a σ * (ascPochhammer ℂ m).eval a := by
  have hpole : ∀ {s : ℂ}, 0 < s.re → ∀ k : ℕ, s ≠ -k := fun {s} hs k h => by
    have := congrArg re h; simp at this; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
  have ham : 0 < (a + m).re := by simp; positivity
  have h1 := Gamma_mul_Gamma_eq_betaIntegral ham hσ
  have h2 := Gamma_mul_Gamma_eq_betaIntegral ha hσ
  have g1 := Gamma_add_nat_div_Gamma_eq a (hpole ha) (n := m)
  have haσ : 0 < (a + σ).re := by simp; linarith
  have g2 := Gamma_add_nat_div_Gamma_eq (a + σ) (hpole haσ) (n := m)
  have hGa := Gamma_ne_zero (hpole ha)
  have hGaσ := Gamma_ne_zero (hpole haσ)
  have hGσ := Gamma_ne_zero (hpole hσ)
  have hGaσm : Gamma (a + m + σ) ≠ 0 := Gamma_ne_zero (hpole (by simp; positivity))
  rw [show a + m + σ = a + σ + m by ring] at h1 hGaσm
  rw [← g1, ← g2]
  have hb1 : betaIntegral (a + m) σ = Gamma (a + m) * Gamma σ / Gamma (a + σ + m) := by
    rw [h1]; field_simp
  have hb2 : betaIntegral a σ = Gamma a * Gamma σ / Gamma (a + σ) := by
    rw [h2]; field_simp
  rw [hb1, hb2]
  field_simp

/-- **Exercise 6.9-7**, in the form of (6.9-6): for `re σ > 0` and `re (β + ½) > 0`,
`B(β + ½, σ) Rₙ(β + σ, β + σ; x + y, x - y) =
∫₀¹ u^{β - 1/2} (1 - u)^{σ - 1} Rₙ(β, β; x + y√u, x - y√u) du`, with both R-polynomials written
as the sums of (6.9-6). -/
theorem integral_evenBinomialSum (n : ℕ) {β σ : ℂ} (hβ : 0 < (β + 1 / 2).re) (hσ : 0 < σ.re)
    (x y : ℂ) :
    ∫ u : ℝ in 0..1, (u : ℂ) ^ (β - 1 / 2) * (1 - (u : ℂ)) ^ (σ - 1) *
        evenBinomialSum n (β + 1 / 2) x (y * (Real.sqrt u : ℂ)) =
      betaIntegral (β + 1 / 2) σ * evenBinomialSum n (β + σ + 1 / 2) x y := by
  set a := β + 1 / 2
  set c : ℕ → ℂ := fun j => if Even j then (n.choose j : ℂ) *
    (ascPochhammer ℂ (j / 2)).eval (1 / 2) / (ascPochhammer ℂ (j / 2)).eval a *
      x ^ (n - j) * y ^ j else 0
  set g : ℕ → ℝ → ℂ := fun j u =>
    c j * ((u : ℂ) ^ (a + (j / 2 : ℕ) - 1) * (1 - (u : ℂ)) ^ (σ - 1))
  have hpt : ∀ u ∈ Set.uIoc (0 : ℝ) 1, (u : ℂ) ^ (β - 1 / 2) * (1 - (u : ℂ)) ^ (σ - 1) *
      evenBinomialSum n a x (y * (Real.sqrt u : ℂ)) = ∑ j ∈ range (n + 1), g j u := by
    intro u hu
    rw [Set.uIoc_of_le zero_le_one] at hu
    have hu0 : (u : ℂ) ≠ 0 := by exact_mod_cast hu.1.ne'
    rw [evenBinomialSum, mul_sum]
    refine sum_congr rfl fun j _ => ?_
    simp only [g, c]
    split_ifs with he
    · obtain ⟨m, rfl⟩ := he
      have hs : ((Real.sqrt u : ℂ)) ^ (2 * m) = (u : ℂ) ^ m := by
        rw [pow_mul, ← ofReal_pow, Real.sq_sqrt hu.1.le]
      rw [show m + m = 2 * m by ring, Nat.mul_div_cancel_left m two_pos, mul_pow, hs,
        show a + (m : ℂ) - 1 = (β - 1 / 2) + m by
          simp only [a]; ring, cpow_add _ _ hu0, cpow_natCast]
      ring
    · simp
  have hint : ∀ j ∈ range (n + 1), IntervalIntegrable (g j) MeasureTheory.volume 0 1 :=
    fun j _ => (betaIntegral_convergent (by simp; positivity) hσ).const_mul _
  rw [intervalIntegral.integral_congr_ae (MeasureTheory.ae_of_all _ hpt),
    intervalIntegral.integral_finsetSum hint, evenBinomialSum, mul_sum]
  refine sum_congr rfl fun j _ => ?_
  simp only [g, c, intervalIntegral.integral_const_mul]
  split_ifs with he
  · have hb := betaIntegral_add_nat_mul hβ hσ (j / 2)
    have ha : (ascPochhammer ℂ (j / 2)).eval a ≠ 0 :=
      ascPochhammer_eval_ne_zero_of_re_pos hβ _
    have haσ : (ascPochhammer ℂ (j / 2)).eval (a + σ) ≠ 0 :=
      ascPochhammer_eval_ne_zero_of_re_pos (by simp only [add_re]; linarith) _
    rw [show β + σ + 1 / 2 = a + σ by simp only [a]; ring]
    change _ * betaIntegral (a + (j / 2 : ℕ)) σ = _
    field_simp
    linear_combination (n.choose j : ℂ) * (ascPochhammer ℂ (j / 2)).eval (1 / 2) *
      x ^ (n - j) * y ^ j * hb
  · simp

/-- **Exercise 6.9-7**: if `re σ > 0`, `re (β + ½) > 0` and `(2β)ₙ`, `(2β + 2σ)ₙ` do not
vanish, then `B(β + ½, σ) Rₙ(β + σ, β + σ; x + y, x - y) =
∫₀¹ u^{β - 1/2} (1 - u)^{σ - 1} Rₙ(β, β; x + y√u, x - y√u) du`, with `Rₙ = Nₙ/(c)ₙ`. -/
theorem betaIntegral_mul_carlsonRPolynomial₂ (n : ℕ) {β σ : ℂ} (hβ : 0 < (β + 1 / 2).re)
    (hσ : 0 < σ.re) (x y : ℂ) (h₁ : (ascPochhammer ℂ n).eval (2 * β) ≠ 0)
    (h₂ : (ascPochhammer ℂ n).eval (2 * (β + σ)) ≠ 0) :
    betaIntegral (β + 1 / 2) σ * (carlsonRPolynomialNumerator₂ n (β + σ) (β + σ) (x + y) (x - y) /
        (ascPochhammer ℂ n).eval (2 * (β + σ))) =
      ∫ u : ℝ in 0..1, (u : ℂ) ^ (β - 1 / 2) * (1 - (u : ℂ)) ^ (σ - 1) *
        (carlsonRPolynomialNumerator₂ n β β (x + y * (Real.sqrt u : ℂ))
          (x - y * (Real.sqrt u : ℂ)) / (ascPochhammer ℂ n).eval (2 * β)) := by
  have hR : ∀ u : ℝ, carlsonRPolynomialNumerator₂ n β β (x + y * (Real.sqrt u : ℂ))
      (x - y * (Real.sqrt u : ℂ)) / (ascPochhammer ℂ n).eval (2 * β) =
        evenBinomialSum n (β + 1 / 2) x (y * (Real.sqrt u : ℂ)) := fun u => by
    rw [carlsonRPolynomialNumerator₂_add_sub_eq_mul n β _ _ h₁, mul_div_cancel_left₀ _ h₁]
  simp_rw [hR]
  rw [integral_evenBinomialSum n hβ hσ, carlsonRPolynomialNumerator₂_add_sub_eq_mul n _ _ _ h₂,
    mul_div_cancel_left₀ _ h₂, show β + σ + 1 / 2 = β + σ + 1 / 2 from rfl]

end Carlson.TwoVariable
