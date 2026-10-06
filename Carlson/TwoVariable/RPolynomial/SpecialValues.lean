/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.TwoVariable.RPolynomial.Hypergeometric
public import Carlson.TwoVariable.Quadratic.Polynomial

/-!
# Special values of two-node R-polynomials (Exercises 6.9-2 and 6.9-6)

Exercise 6.9-2 evaluates `R_n(β, 1 - 2β - n; 2, 1)` and three terminating `₂F₁` series at the
points `2`, `-1` and `½`; Exercise 6.9-6 expands `Rₙ(β, β; x + y, x - y)` in powers of `y`. The
R-polynomial statements are given for the Pochhammer numerator `Nₙ = (c)ₙ Rₙ`, which holds for
all parameters; the hypergeometric statements assume the stated denominators do not vanish.

## Main results

* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_odd_two_one`,
  `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_even_two_one`: Exercise 6.9-2 (1), (2).
* `Carlson.TwoVariable.ordinaryHypergeometric_two`,
  `Carlson.TwoVariable.ordinaryHypergeometric_neg_one`,
  `Carlson.TwoVariable.ordinaryHypergeometric_half`: Exercise 6.9-2 (3)–(5).
* `Carlson.TwoVariable.carlsonRPolynomialNumerator₂_add_sub`: Exercise 6.9-6.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977, §6.9.
-/

open Complex Finset
@[expose] public noncomputable section
namespace Carlson.TwoVariable

/-- `4ⁿ (½)ₙ n! = (2n)!`. -/
theorem four_pow_mul_ascPochhammer_half (n : ℕ) :
    (4 : ℂ) ^ n * (ascPochhammer ℂ n).eval (1 / 2) * (n.factorial : ℂ) =
      ((2 * n).factorial : ℂ) := by
  have h := ascPochhammer_eval_double (1 / 2 : ℂ) n
  rw [show (2 : ℂ) * (1 / 2) = 1 by norm_num, show (1 / 2 : ℂ) + 1 / 2 = 1 by norm_num,
    ascPochhammer_eval_one, ascPochhammer_eval_one] at h
  rw [h]

/-- `N_n(β, 1 - 2β - n; 2, 1) = (-1)ⁿ Nₙ(β, β; 1, -1)`. -/
theorem carlsonRPolynomialNumerator₂_two_one (n : ℕ) (β : ℂ) :
    carlsonRPolynomialNumerator₂ n β (1 - 2 * β - n) 2 1 =
      (-1) ^ n * carlsonRPolynomialNumerator₂ n β β 1 (-1) := by
  rw [carlsonRPolynomialNumerator₂_linear n β β 1 (-1), ← carlsonRPolynomialNumerator₂_swap,
    show (1 : ℂ) - β - β - n = 1 - 2 * β - n by ring, show (1 : ℂ) - -1 = 2 by norm_num,
    ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Exercise 6.9-2 (1)**: `R_{2n+1}(β, -2β - 2n; 2, 1) = 0`, in numerator form. -/
theorem carlsonRPolynomialNumerator₂_odd_two_one (n : ℕ) (β : ℂ) :
    carlsonRPolynomialNumerator₂ (2 * n + 1) β (-2 * β - 2 * n) 2 1 = 0 := by
  have h := carlsonRPolynomialNumerator₂_two_one (2 * n + 1) β
  rw [show (1 : ℂ) - 2 * β - ((2 * n + 1 : ℕ) : ℂ) = -2 * β - 2 * n by push_cast; ring,
    carlsonRPolynomialNumerator₂_eq_zero_of_odd _ ⟨n, rfl⟩, mul_zero] at h
  exact h

/-- **Exercise 6.9-2 (2)**: `R_{2n}(β, 1 - 2β - 2n; 2, 1) = (2n)! (β)ₙ/(n! (β)_{2n})` if
`(β)_{2n} ≠ 0`. Here `R = N/(1 - β - 2n)_{2n}` and `(1 - β - 2n)_{2n} = (β)_{2n}`. -/
theorem carlsonRPolynomialNumerator₂_even_two_one (n : ℕ) (β : ℂ)
    (hβ : (ascPochhammer ℂ (2 * n)).eval β ≠ 0) :
    carlsonRPolynomialNumerator₂ (2 * n) β (1 - 2 * β - 2 * n) 2 1 /
        (ascPochhammer ℂ (2 * n)).eval (β + (1 - 2 * β - 2 * n)) =
      ((2 * n).factorial : ℂ) * (ascPochhammer ℂ n).eval β /
        ((n.factorial : ℂ) * (ascPochhammer ℂ (2 * n)).eval β) := by
  have h := carlsonRPolynomialNumerator₂_two_one (2 * n) β
  have hop := numerator₂_even_opposite n β 1
  have hrefl : (ascPochhammer ℂ (2 * n)).eval (β + (1 - 2 * β - 2 * n)) =
      (ascPochhammer ℂ (2 * n)).eval β := by
    rw [show β + (1 - 2 * β - 2 * n) = 1 - β - ((2 * n : ℕ) : ℂ) by push_cast; ring,
      ascPochhammer_eval_reflect, pow_mul]
    norm_num
  rw [show (1 : ℂ) - 2 * β - ((2 * n : ℕ) : ℂ) = 1 - 2 * β - 2 * n by push_cast; ring,
    pow_mul, show ((-1 : ℂ) ^ 2) = 1 by norm_num, one_pow, one_mul, hop, one_pow, mul_one] at h
  rw [h, hrefl, ← four_pow_mul_ascPochhammer_half n]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

/-- **Exercise 6.9-2 (3)**: `₂F₁(-2n, β; 2β; 2) = (½)ₙ/(β + ½)ₙ` if `(2β)_{2n} ≠ 0`. -/
theorem ordinaryHypergeometric_two (n : ℕ) (β : ℂ)
    (hβ : (ascPochhammer ℂ (2 * n)).eval (2 * β) ≠ 0) :
    ordinaryHypergeometric (-((2 * n : ℕ) : ℂ)) β (2 * β) 2 =
      (ascPochhammer ℂ n).eval (1 / 2) / (ascPochhammer ℂ n).eval (β + 1 / 2) := by
  have h := carlsonRPolynomialNumerator₂_eq_hypergeometric (2 * n) β β (-1) one_ne_zero
    (by rwa [← two_mul])
  have hop := numerator₂_even_opposite n β (-1)
  rw [neg_neg, ← carlsonRPolynomialNumerator₂_swap] at hop
  rw [show (1 : ℂ) - -1 / 1 = 2 by norm_num, one_pow, mul_one, ← two_mul,
    carlsonRPolynomialNumerator₂_swap, hop, ascPochhammer_eval_double] at h
  have hd := ascPochhammer_eval_double β n
  rw [hd] at hβ
  have h1 : (ascPochhammer ℂ n).eval (β + 1 / 2) ≠ 0 := fun h0 => hβ (by rw [h0, mul_zero])
  have h2 : (4 : ℂ) ^ n * (ascPochhammer ℂ n).eval β ≠ 0 := fun h0 => hβ (by rw [h0, zero_mul])
  rw [eq_div_iff h1]
  apply mul_left_cancel₀ h2
  rw [neg_one_pow_eq_one_iff_even (by norm_num) |>.mpr ⟨n, by ring⟩] at h
  linear_combination -h

/-- `(1 - β - 2n)_{2n} = (β)_{2n}`. -/
theorem ascPochhammer_eval_one_sub_sub_two_mul (n : ℕ) (β : ℂ) :
    (ascPochhammer ℂ (2 * n)).eval (1 - β - ((2 * n : ℕ) : ℂ)) =
      (ascPochhammer ℂ (2 * n)).eval β := by
  rw [ascPochhammer_eval_reflect, pow_mul]; norm_num

/-- **Exercise 6.9-2 (4)**: `₂F₁(-2n, β; 1 - β - 2n; -1) = (2n)! (β)ₙ/(n! (β)_{2n})` if
`(β)_{2n} ≠ 0`. -/
theorem ordinaryHypergeometric_neg_one (n : ℕ) (β : ℂ)
    (hβ : (ascPochhammer ℂ (2 * n)).eval β ≠ 0) :
    ordinaryHypergeometric (-((2 * n : ℕ) : ℂ)) β (1 - β - ((2 * n : ℕ) : ℂ)) (-1) =
      ((2 * n).factorial : ℂ) * (ascPochhammer ℂ n).eval β /
        ((n.factorial : ℂ) * (ascPochhammer ℂ (2 * n)).eval β) := by
  have h := carlsonRPolynomialNumerator₂_eq_hypergeometric_div (2 * n) β β (-1) one_ne_zero
    (by rwa [ascPochhammer_eval_one_sub_sub_two_mul])
  have hop := numerator₂_even_opposite n β 1
  rw [← carlsonRPolynomialNumerator₂_swap] at h
  rw [one_pow, mul_one, div_one, hop, one_pow, mul_one] at h
  have hN := h
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [eq_div_iff (mul_ne_zero hf hβ), ← four_pow_mul_ascPochhammer_half n]
  linear_combination -(n.factorial : ℂ) * hN

/-- **Exercise 6.9-2 (5)**: `₂F₁(-2n, 1 - 2β - 2n; 1 - β - 2n; ½) = (½)ₙ (β)ₙ/(β)_{2n}` if
`(β)_{2n} ≠ 0`. -/
theorem ordinaryHypergeometric_half (n : ℕ) (β : ℂ)
    (hβ : (ascPochhammer ℂ (2 * n)).eval β ≠ 0) :
    ordinaryHypergeometric (-((2 * n : ℕ) : ℂ)) (1 - 2 * β - ((2 * n : ℕ) : ℂ))
        (1 - β - ((2 * n : ℕ) : ℂ)) (1 / 2) =
      (ascPochhammer ℂ n).eval (1 / 2) * (ascPochhammer ℂ n).eval β /
        (ascPochhammer ℂ (2 * n)).eval β := by
  have h := carlsonRPolynomialNumerator₂_eq_hypergeometric_sub (2 * n) β β (x := 1) (y := -1)
    (by norm_num) (by rwa [ascPochhammer_eval_one_sub_sub_two_mul])
  have hop := numerator₂_even_opposite n β 1
  rw [hop, one_pow, mul_one, show (1 : ℂ) / (1 - -1) = 1 / 2 by norm_num,
    show (-1 : ℂ) - 1 = -2 by norm_num, show 1 - (β + β) = 1 - 2 * β by ring, pow_mul,
    show ((-2 : ℂ)) ^ 2 = 4 by norm_num] at h
  rw [eq_div_iff hβ]
  have h4 : (4 : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
  apply mul_left_cancel₀ h4
  linear_combination -h

/-- **Exercise 6.9-6**, division-free form: by the binomial theorem with the opposite nodes
`y, -y`, `Nₙ(β, β; x + y, x - y) = ∑ⱼ (n choose j) xⁿ⁻ʲ (2β + j)_(n-j) Nⱼ(β, β; y, -y)`, where
`N_{2m}(β, β; y, -y) = 4ᵐ (β)ₘ (½)ₘ y^{2m}` and the odd terms vanish. Dividing by `(2β)ₙ` gives
Carlson's `Rₙ(β, β; x + y, x - y) = ∑ₘ (n choose 2m) (½)ₘ/(β + ½)ₘ x^(n-2m) y^{2m}`. -/
theorem carlsonRPolynomialNumerator₂_add_sub (n : ℕ) (β x y : ℂ) :
    carlsonRPolynomialNumerator₂ n β β (x + y) (x - y) = ∑ j ∈ range (n + 1),
      (n.choose j : ℂ) * x ^ (n - j) * (ascPochhammer ℂ (n - j)).eval (2 * β + j) *
        (if Even j then 4 ^ (j / 2) * (ascPochhammer ℂ (j / 2)).eval β *
          (ascPochhammer ℂ (j / 2)).eval (1 / 2) * y ^ j else 0) := by
  have h := carlsonRPolynomialNumerator₂_add_const n β β y (-y) x
  rw [add_comm y x, show -y + x = x - y by ring] at h
  rw [h]
  refine sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · obtain ⟨m, rfl⟩ := hj
    rw [show m + m = 2 * m by ring, numerator₂_even_opposite, Nat.mul_div_cancel_left m two_pos,
      show β + β = 2 * β by ring]
  · rw [carlsonRPolynomialNumerator₂_eq_zero_of_odd _ (Nat.not_even_iff_odd.mp hj)]; simp
