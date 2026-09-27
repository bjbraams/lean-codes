/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.Endpoints

/-!
# The three-term recurrence of Jacobi polynomials

The shifted Jacobi polynomials satisfy the classical three-term recurrence at every
parameter, in a form without denominators. Dividing by the leading coefficients gives
Carlson's recurrence for the monic polynomials with arbitrary endpoints `r, s`:
`p_{n+2}(x) = (x - V_{n+1}) p_{n+1}(x) - W_{n+1} p_n(x)`.

## Main results

* `Polynomial.shiftedJacobi_three_term`: the denominator-free recurrence over a field of
  characteristic zero.
* `Polynomial.eval_jacobiOn_three_term`: Carlson's monic recurrence at arbitrary endpoints.
* `Polynomial.jacobiOn_three_term`: the same recurrence as a polynomial identity.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Exercise 7.1-6.
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K] [CharZero K]

omit [CharZero K] in
/-- Peeling the first factor of an evaluated rising factorial. -/
private theorem eval_ascPochhammer_succ_left' (a : K) (m : ℕ) :
    (ascPochhammer K (m + 1)).eval a = a * (ascPochhammer K m).eval (a + 1) := by
  simp only [ascPochhammer_succ_left, eval_mul, eval_X, eval_comp, eval_add, eval_one]

omit [CharZero K] in
private theorem factorial_succ_cast (m : ℕ) : ((m + 1).factorial : K) = (m + 1) * m.factorial := by
  push_cast [Nat.factorial_succ]; ring

omit [CharZero K] in
private theorem factorial_add_two_cast (m : ℕ) :
    ((m + 2).factorial : K) = (m + 2) * ((m + 1) * m.factorial) := by
  rw [show m + 2 = (m + 1) + 1 by rfl, factorial_succ_cast, factorial_succ_cast]; push_cast; ring

/-- The three-term coefficient identity at the constant term. -/
private theorem three_term_coeff_zero (α β : K) (n : ℕ) :
    2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) * jacobiCoeff α β (n + 2) 0 =
      (α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2)) *
          jacobiCoeff α β (n + 1) 0
        - 2 * (α + n + 1) * (β + n + 1) * (α + β + 2 * n + 4) * jacobiCoeff α β n 0 := by
  simp only [jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  push_cast
  set A := eval (α + 0 + 1) (ascPochhammer K n)
  have h1 : eval (α + 0 + 1) (ascPochhammer K (n + 2)) = A * (α + 1 + n) * (α + 2 + n) := by
    simp only [ascPochhammer_succ_eval, A]; push_cast; ring
  have h2 : eval (α + 0 + 1) (ascPochhammer K (n + 1)) = A * (α + 1 + n) := by
    simp only [ascPochhammer_succ_eval, A]; ring
  rw [h1, h2, factorial_add_two_cast n, factorial_succ_cast n]
  clear_value A
  simp only [pow_zero, ascPochhammer_zero, eval_one, Nat.factorial_zero, Nat.cast_one]
  generalize hI : (n : K) = I at *
  have hI1 : I + 1 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero n
  have hI2 : I + 2 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero (n + 1)
  generalize (n.factorial : K) = F at *
  by_cases hF : F = 0
  · simp [hF]
  field_simp
  ring

/-- The three-term coefficient identity at the linear term, for positive index. -/
private theorem three_term_coeff_one (α β : K) (i : ℕ) :
    let n := i + 1
    2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) * jacobiCoeff α β (i + 2) 1 =
      (α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2)) *
          jacobiCoeff α β (i + 1) 1
        - 2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2) *
          jacobiCoeff α β (i + 2) 0
        - 2 * (α + n + 1) * (β + n + 1) * (α + β + 2 * n + 4) * jacobiCoeff α β i 1 := by
  intro n
  simp only [n, jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  push_cast
  set A := eval (α + 1 + 1) (ascPochhammer K i)
  have h1 : eval (α + 1 + 1) (ascPochhammer K (i + 2)) = A * (α + 2 + i) * (α + 3 + i) := by
    simp only [ascPochhammer_succ_eval, A]; push_cast; ring
  have h2 : eval (α + 1 + 1) (ascPochhammer K (i + 1)) = A * (α + 2 + i) := by
    simp only [ascPochhammer_succ_eval, A]; ring
  have h3 : eval (α + 0 + 1) (ascPochhammer K (i + 2)) = (α + 1) * (A * (α + 2 + i)) := by
    rw [eval_ascPochhammer_succ_left', show α + 0 + 1 + 1 = α + 1 + 1 by ring, h2]; ring
  rw [h1, h2, h3, factorial_add_two_cast i, factorial_succ_cast i]
  clear_value A
  simp only [pow_zero, pow_one, ascPochhammer_zero, eval_one, ascPochhammer_one, eval_X,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
  generalize hI : (i : K) = I at *
  have hI1 : I + 1 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero i
  have hI2 : I + 2 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero (i + 1)
  generalize (i.factorial : K) = F at *
  by_cases hF : F = 0
  · simp [hF]
  field_simp
  ring

/-- The three-term coefficient identity at an interior index. -/
private theorem three_term_coeff_mid (α β : K) (i j : ℕ) :
    let n := i + j + 2
    2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) * jacobiCoeff α β (i + 2) (j + 2) =
      (α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2)) *
          jacobiCoeff α β (i + 1) (j + 2)
        - 2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2) *
          jacobiCoeff α β (i + 2) (j + 1)
        - 2 * (α + n + 1) * (β + n + 1) * (α + β + 2 * n + 4) * jacobiCoeff α β i (j + 2) := by
  intro n
  simp only [n, jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  push_cast
  set A := eval (α + (↑j + 2) + 1) (ascPochhammer K i)
  set B := eval (α + β + (↑i + 2 + (↑j + 2)) + 1) (ascPochhammer K j)
  have h1 : eval (α + (↑j + 2) + 1) (ascPochhammer K (i + 2)) =
      A * (α + j + 3 + i) * (α + j + 4 + i) := by
    simp only [ascPochhammer_succ_eval, A]; push_cast; ring
  have h2 : eval (α + (↑j + 2) + 1) (ascPochhammer K (i + 1)) = A * (α + j + 3 + i) := by
    simp only [ascPochhammer_succ_eval, A]; ring
  have h3 : eval (α + (↑j + 1) + 1) (ascPochhammer K (i + 2)) =
      (α + j + 2) * (A * (α + j + 3 + i)) := by
    rw [eval_ascPochhammer_succ_left', show α + (↑j + 1) + 1 + 1 = α + (↑j + 2) + 1 by ring, h2]
    ring
  have h4 : eval (α + β + (↑i + 2 + (↑j + 2)) + 1) (ascPochhammer K (j + 2)) =
      B * (α + β + i + 2 * j + 5) * (α + β + i + 2 * j + 6) := by
    simp only [ascPochhammer_succ_eval, B]; push_cast; ring
  have h5 : eval (α + β + (↑i + 1 + (↑j + 2)) + 1) (ascPochhammer K (j + 2)) =
      (α + β + i + j + 4) * (B * (α + β + i + 2 * j + 5)) := by
    rw [eval_ascPochhammer_succ_left',
      show α + β + (↑i + 1 + (↑j + 2)) + 1 + 1 = α + β + (↑i + 2 + (↑j + 2)) + 1 by ring,
      ascPochhammer_succ_eval]
    ring
  have h6 : eval (α + β + (↑i + 2 + (↑j + 1)) + 1) (ascPochhammer K (j + 1)) =
      (α + β + i + j + 4) * B := by
    rw [eval_ascPochhammer_succ_left',
      show α + β + (↑i + 2 + (↑j + 1)) + 1 + 1 = α + β + (↑i + 2 + (↑j + 2)) + 1 by ring]
    ring
  have h7 : eval (α + β + (↑i + (↑j + 2)) + 1) (ascPochhammer K (j + 2)) =
      (α + β + i + j + 3) * ((α + β + i + j + 4) * B) := by
    rw [eval_ascPochhammer_succ_left', eval_ascPochhammer_succ_left',
      show α + β + (↑i + (↑j + 2)) + 1 + 1 + 1 = α + β + (↑i + 2 + (↑j + 2)) + 1 by ring]
    ring
  rw [h1, h2, h3, h4, h5, h6, h7, factorial_add_two_cast i, factorial_add_two_cast j,
    factorial_succ_cast i, factorial_succ_cast j]
  clear_value A B
  rw [pow_succ, pow_succ, pow_succ]
  generalize ((-1 : K) ^ j) = σ
  generalize hI : (i : K) = I at *
  generalize hJ : (j : K) = J at *
  have hI1 : I + 1 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero i
  have hI2 : I + 2 ≠ 0 := by rw [← hI]; exact_mod_cast Nat.succ_ne_zero (i + 1)
  have hJ1 : J + 1 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero j
  have hJ2 : J + 2 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero (j + 1)
  generalize (i.factorial : K) = F at *
  generalize (j.factorial : K) = G at *
  by_cases hF : F = 0
  · simp [hF]
  by_cases hG : G = 0
  · simp [hG]
  field_simp
  ring

/-- The three-term coefficient identity one step above the lowest degree, index zero. -/
private theorem three_term_coeff_top_zero (α β : K) :
    2 * ((0 : ℕ) + (2 : K)) * (α + β + (0 : ℕ) + 2) * (α + β + 2 * (0 : ℕ) + 2) *
        jacobiCoeff α β 1 1 =
      (α + β + 2 * (0 : ℕ) + 3) * ((α + β + 2 * (0 : ℕ) + 4) * (α + β + 2 * (0 : ℕ) + 2) +
          (α ^ 2 - β ^ 2)) * jacobiCoeff α β 0 1
        - 2 * (α + β + 2 * (0 : ℕ) + 3) * (α + β + 2 * (0 : ℕ) + 4) * (α + β + 2 * (0 : ℕ) + 2) *
          jacobiCoeff α β 1 0 := by
  simp only [jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  simp only [ascPochhammer_zero, ascPochhammer_one, eval_one, eval_X, pow_zero, pow_one,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one, Nat.cast_zero]
  push_cast
  ring

/-- The three-term coefficient identity one step above the lowest degree. -/
private theorem three_term_coeff_top (α β : K) (m : ℕ) :
    let n := m + 1
    2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) * jacobiCoeff α β 1 (m + 2) =
      (α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2)) *
          jacobiCoeff α β 0 (m + 2)
        - 2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2) *
          jacobiCoeff α β 1 (m + 1) := by
  intro n
  simp only [n, jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  push_cast
  set B := eval (α + β + (1 + (↑m + 2)) + 1) (ascPochhammer K m)
  have h1 : eval (α + β + (1 + (↑m + 2)) + 1) (ascPochhammer K (m + 2)) =
      B * (α + β + 2 * m + 4) * (α + β + 2 * m + 5) := by
    simp only [ascPochhammer_succ_eval, B]; push_cast; ring
  have h2 : eval (α + β + (0 + (↑m + 2)) + 1) (ascPochhammer K (m + 2)) =
      (α + β + m + 3) * (B * (α + β + 2 * m + 4)) := by
    rw [eval_ascPochhammer_succ_left',
      show α + β + (0 + (↑m + 2)) + 1 + 1 = α + β + (1 + (↑m + 2)) + 1 by ring,
      ascPochhammer_succ_eval]
    ring
  have h3 : eval (α + β + (1 + (↑m + 1)) + 1) (ascPochhammer K (m + 1)) =
      (α + β + m + 3) * B := by
    rw [eval_ascPochhammer_succ_left',
      show α + β + (1 + (↑m + 1)) + 1 + 1 = α + β + (1 + (↑m + 2)) + 1 by ring]
    ring
  rw [h1, h2, h3, factorial_add_two_cast m, factorial_succ_cast m]
  clear_value B
  simp only [ascPochhammer_zero, ascPochhammer_one, eval_one, eval_X,
    Nat.factorial_zero, Nat.factorial_one, Nat.cast_one]
  rw [pow_succ, pow_succ, pow_succ]
  generalize ((-1 : K) ^ m) = σ
  generalize hJ : (m : K) = J at *
  have hJ1 : J + 1 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero m
  have hJ2 : J + 2 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero (m + 1)
  generalize (m.factorial : K) = G at *
  by_cases hG : G = 0
  · simp [hG]
  field_simp
  ring

/-- The three-term coefficient identity at the leading degree. -/
private theorem three_term_coeff_lead (α β : K) (n : ℕ) :
    2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) * jacobiCoeff α β 0 (n + 2) =
      - 2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2) *
          jacobiCoeff α β 0 (n + 1) := by
  simp only [jacobiCoeff, map_div₀, map_pow, map_neg, map_one, map_mul, map_natCast]
  push_cast
  set B := eval (α + β + (0 + (↑n + 2)) + 1) (ascPochhammer K n)
  have h1 : eval (α + β + (0 + (↑n + 2)) + 1) (ascPochhammer K (n + 2)) =
      B * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) := by
    simp only [ascPochhammer_succ_eval, B]; push_cast; ring
  have h2 : eval (α + β + (0 + (↑n + 1)) + 1) (ascPochhammer K (n + 1)) =
      (α + β + n + 2) * B := by
    rw [eval_ascPochhammer_succ_left',
      show α + β + (0 + (↑n + 1)) + 1 + 1 = α + β + (0 + (↑n + 2)) + 1 by ring]
    ring
  rw [h1, h2, factorial_add_two_cast n, factorial_succ_cast n]
  clear_value B
  simp only [ascPochhammer_zero, eval_one, Nat.factorial_zero, Nat.cast_one]
  rw [pow_succ, pow_succ]
  generalize ((-1 : K) ^ n) = σ
  generalize hJ : (n : K) = J at *
  have hJ1 : J + 1 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero n
  have hJ2 : J + 2 ≠ 0 := by rw [← hJ]; exact_mod_cast Nat.succ_ne_zero (n + 1)
  generalize (n.factorial : K) = G at *
  by_cases hG : G = 0
  · simp [hG]
  field_simp

/-- The three-term recurrence of shifted Jacobi polynomials over a field of characteristic
zero, in denominator-free form. It holds at every parameter, including exceptional ones. -/
theorem shiftedJacobi_three_term (α β : K) (n : ℕ) :
    C (2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2)) * shiftedJacobi α β (n + 2) =
      C ((α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2))) *
          shiftedJacobi α β (n + 1)
        - C (2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2)) *
          (X * shiftedJacobi α β (n + 1))
        - C (2 * (α + n + 1) * (β + n + 1) * (α + β + 2 * n + 4)) * shiftedJacobi α β n := by
  ext k
  simp only [coeff_sub, coeff_C_mul]
  rcases k with _ | k
  · simp only [coeff_X_mul_zero, mul_zero, sub_zero, coeff_shiftedJacobi, Nat.zero_le,
      ite_true, Nat.sub_zero]
    exact three_term_coeff_zero α β n
  rcases k with _ | k
  · rcases n with _ | i
    · simp only [coeff_X_mul, coeff_shiftedJacobi]
      norm_num only [ite_true, ite_false, le_refl, Nat.one_le_iff_ne_zero]
      simp only [mul_zero, sub_zero]
      have h := three_term_coeff_top_zero α β
      push_cast at h
      linear_combination h
    · simp only [coeff_X_mul, coeff_shiftedJacobi]
      rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
        ite_eq_left (by omega),
        show i + 1 + 2 - (0 + 1) = i + 2 by omega, show i + 1 + 1 - (0 + 1) = i + 1 by omega,
        show i + 1 + 1 - 0 = i + 2 by omega, show i + 1 - (0 + 1) = i by omega]
      exact three_term_coeff_one α β i
  simp only [coeff_X_mul, coeff_shiftedJacobi]
  rcases le_or_gt (k + 2) n with h | h
  · obtain ⟨i, rfl⟩ : ∃ i, n = i + k + 2 := ⟨n - (k + 2), by omega⟩
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_left (by omega),
      show i + k + 2 + 2 - (k + 1 + 1) = i + 2 by omega,
      show i + k + 2 + 1 - (k + 1 + 1) = i + 1 by omega,
      show i + k + 2 + 1 - (k + 1) = i + 2 by omega, show i + k + 2 - (k + 1 + 1) = i by omega]
    exact three_term_coeff_mid α β i k
  rcases (show n = k + 1 ∨ n = k ∨ n < k by omega) with h1 | h1 | h'
  · subst h1
    rw [ite_eq_left (by omega), ite_eq_left (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega),
      show k + 1 + 2 - (k + 1 + 1) = 1 by omega, show k + 1 + 1 - (k + 1 + 1) = 0 by omega,
      show k + 1 + 1 - (k + 1) = 1 by omega, mul_zero, sub_zero]
    exact three_term_coeff_top α β k
  · subst h1
    rw [ite_eq_left (by omega), ite_eq_right (by omega), ite_eq_left (by omega),
      ite_eq_right (by omega),
      show n + 2 - (n + 1 + 1) = 0 by omega, show n + 1 - (n + 1) = 0 by omega,
      mul_zero, mul_zero, sub_zero, zero_sub]
    rw [three_term_coeff_lead α β n]
    ring
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]
    ring


/-- Carlson's recurrence coefficient `V_{n+1}` for monic Jacobi polynomials with endpoints
`r, s`. -/
def jacobiRecurrenceV (α β r s : K) (n : ℕ) : K :=
  (α ^ 2 - β ^ 2) * (r - s) / (2 * (α + β + 2 * n + 2) * (α + β + 2 * n + 4)) + (r + s) / 2

/-- Carlson's recurrence coefficient `W_{n+1}` for monic Jacobi polynomials with endpoints
`r, s`. -/
def jacobiRecurrenceW (α β r s : K) (n : ℕ) : K :=
  (n + 1) * (α + n + 1) * (β + n + 1) * (α + β + n + 1) * (r - s) ^ 2 /
    ((α + β + 2 * n + 2) ^ 2 * (α + β + 2 * n + 1) * (α + β + 2 * n + 3))

/-- Carlson's three-term recurrence (Exercise 7.1-6) for monic Jacobi polynomials with
arbitrary endpoints, including coincident ones. The hypotheses say that the three
polynomials are monic of full degree and that the recurrence coefficients are defined. -/
theorem eval_jacobiOn_three_term (α β r s x : K) (n : ℕ)
    (h₀ : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0)
    (h₁ : (ascPochhammer K (n + 1)).eval (α + β + (n + 1 : ℕ) + 1) ≠ 0)
    (h₂ : (ascPochhammer K (n + 2)).eval (α + β + (n + 2 : ℕ) + 1) ≠ 0)
    (hd : α + β + 2 * n + 1 ≠ 0) :
    (jacobiOn α β r s (n + 2)).eval x =
      (x - jacobiRecurrenceV α β r s n) * (jacobiOn α β r s (n + 1)).eval x -
        jacobiRecurrenceW α β r s n * (jacobiOn α β r s n).eval x := by
  have h₀' := h₀
  have h₁' := h₁
  have h₂' := h₂
  set Q := (ascPochhammer K n).eval (α + β + n + 3)
  have e1 : (ascPochhammer K n).eval (α + β + n + 1) *
      ((α + β + 2 * n + 1) * (α + β + 2 * n + 2)) = (α + β + n + 1) * (α + β + n + 2) * Q := by
    have h := congrArg (fun p : K[X] => p.eval (α + β + n + 1))
      (show ascPochhammer K (n + 2) = ascPochhammer K (n + 2) from rfl)
    have h1 : (ascPochhammer K (n + 2)).eval (α + β + n + 1) =
        (ascPochhammer K n).eval (α + β + n + 1) * (α + β + n + 1 + n) *
          (α + β + n + 1 + (n + 1 : ℕ)) := by
      simp only [ascPochhammer_succ_eval]
    have h2 : (ascPochhammer K (n + 2)).eval (α + β + n + 1) =
        (α + β + n + 1) * ((α + β + n + 1 + 1) * Q) := by
      rw [eval_ascPochhammer_succ_left', eval_ascPochhammer_succ_left',
        show α + β + n + 1 + 1 + 1 = α + β + n + 3 by ring]
    rw [h1] at h2
    push_cast at h2
    linear_combination h2
  have e2 : (ascPochhammer K (n + 1)).eval (α + β + (n + 1 : ℕ) + 1) = (α + β + n + 2) * Q := by
    rw [eval_ascPochhammer_succ_left']
    push_cast
    rw [show α + β + (n + 1) + 1 + 1 = α + β + n + 3 by ring]
    ring
  have e3 : (ascPochhammer K (n + 2)).eval (α + β + (n + 2 : ℕ) + 1) =
      Q * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) := by
    simp only [ascPochhammer_succ_eval]
    push_cast
    rw [show α + β + (n + 2) + 1 = α + β + n + 3 by ring]
    ring
  rw [e3] at h₂
  rw [e2] at h₁
  have hQ : Q ≠ 0 := by intro h; apply h₂; rw [h]; ring
  have hc2 : α + β + n + 2 ≠ 0 := by intro h; apply h₁; rw [h]; ring
  have hd3 : α + β + 2 * n + 3 ≠ 0 := by intro h; apply h₂; rw [h]; ring
  have hd4 : α + β + 2 * n + 4 ≠ 0 := by intro h; apply h₂; rw [h]; ring
  have hd2 : α + β + 2 * n + 2 ≠ 0 := by
    have : (ascPochhammer K (n + 1)).eval (α + β + (n + 1 : ℕ) + 1) =
        (ascPochhammer K n).eval (α + β + (n + 1 : ℕ) + 1) * (α + β + 2 * n + 2) := by
      rw [ascPochhammer_succ_eval]; push_cast; ring
    intro h
    rw [e2, h, mul_zero] at this
    exact h₁ this
  have hc1 : α + β + n + 1 ≠ 0 := by
    intro h
    have h' : (α + β + n + 1) * (α + β + n + 2) * Q = 0 := by rw [h]; ring
    rw [← e1] at h'
    exact mul_ne_zero h₀ (mul_ne_zero hd hd2) h'
  by_cases hrs : r = s
  · subst hrs
    rw [jacobiOn_self α β r (n + 2) h₂', jacobiOn_self α β r (n + 1) h₁',
      jacobiOn_self α β r n h₀']
    simp only [jacobiRecurrenceV, jacobiRecurrenceW, sub_self, mul_zero, zero_div, zero_add,
      eval_pow, eval_sub, eval_X, eval_C]
    ring
  have hd0 : r - s ≠ 0 := sub_ne_zero.mpr hrs
  obtain ⟨y, rfl⟩ : ∃ y, x = (r - s) * y + s := ⟨(x - s) / (r - s), by field_simp; ring⟩
  rw [eval_jacobiOn_affine α β r s y (n + 2) h₂', eval_jacobiOn_affine α β r s y (n + 1) h₁',
    eval_jacobiOn_affine α β r s y n h₀']
  have hrec := congrArg (eval y) (shiftedJacobi_three_term α β n)
  simp only [eval_mul, eval_C, eval_sub, eval_X] at hrec
  have hL : 2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2) ≠ 0 := by
    have : (n : K) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero this) hc2) hd2
  have hS : eval y (shiftedJacobi α β (n + 2)) =
      ((α + β + 2 * n + 3) * ((α + β + 2 * n + 4) * (α + β + 2 * n + 2) + (α ^ 2 - β ^ 2)) *
          eval y (shiftedJacobi α β (n + 1)) -
        2 * (α + β + 2 * n + 3) * (α + β + 2 * n + 4) * (α + β + 2 * n + 2) *
          (y * eval y (shiftedJacobi α β (n + 1))) -
      2 * (α + n + 1) * (β + n + 1) * (α + β + 2 * n + 4) * eval y (shiftedJacobi α β n)) /
        (2 * ((n : K) + 2) * (α + β + n + 2) * (α + β + 2 * n + 2)) := by
    rw [eq_div_iff hL, mul_comm]; exact hrec
  rw [hS]
  have e0 : (ascPochhammer K n).eval (α + β + n + 1) =
      (α + β + n + 1) * (α + β + n + 2) * Q / ((α + β + 2 * n + 1) * (α + β + 2 * n + 2)) := by
    rw [eq_div_iff (mul_ne_zero hd hd2), e1]
  rw [e0, e2, e3]
  have f1 : ((n + 1).factorial : K) = (n + 1) * n.factorial := by
    push_cast [Nat.factorial_succ]; ring
  have f2 : ((n + 2).factorial : K) = (n + 2) * ((n + 1) * n.factorial) := by
    rw [show n + 2 = (n + 1) + 1 by rfl]; push_cast [Nat.factorial_succ]; ring
  rw [f1, f2]
  simp only [jacobiRecurrenceV, jacobiRecurrenceW]
  have hF : (n.factorial : K) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  have hn1 : (n : K) + 1 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have hn2 : (n : K) + 2 ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (n + 1)
  clear_value Q
  simp only [pow_succ]
  have hσ : ((-1 : K) ^ n) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hD : (r - s) ^ n ≠ 0 := pow_ne_zero _ hd0
  generalize ((-1 : K) ^ n) = σ at *
  generalize (r - s) ^ n = D at *
  generalize eval y (shiftedJacobi α β n) = S0
  generalize eval y (shiftedJacobi α β (n + 1)) = S1
  generalize hN : (n : K) = N at *
  generalize (n.factorial : K) = F at *
  have k1 : α + β + N * 2 + 1 ≠ 0 := by rwa [mul_comm]
  have k2 : α + β + N * 2 + 2 ≠ 0 := by rwa [mul_comm]
  have k3 : α + β + N * 2 + 3 ≠ 0 := by rwa [mul_comm]
  have k4 : α + β + N * 2 + 4 ≠ 0 := by rwa [mul_comm]
  field_simp
  ring

/-- Carlson's monic three-term recurrence as an identity of polynomials. -/
theorem jacobiOn_three_term (α β r s : K) (n : ℕ)
    (h₀ : (ascPochhammer K n).eval (α + β + n + 1) ≠ 0)
    (h₁ : (ascPochhammer K (n + 1)).eval (α + β + (n + 1 : ℕ) + 1) ≠ 0)
    (h₂ : (ascPochhammer K (n + 2)).eval (α + β + (n + 2 : ℕ) + 1) ≠ 0)
    (hd : α + β + 2 * n + 1 ≠ 0) :
    jacobiOn α β r s (n + 2) =
      (X - C (jacobiRecurrenceV α β r s n)) * jacobiOn α β r s (n + 1) -
        C (jacobiRecurrenceW α β r s n) * jacobiOn α β r s n := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  simp only [eval_sub, eval_mul, eval_X, eval_C]
  exact eval_jacobiOn_three_term α β r s x n h₀ h₁ h₂ hd

end Polynomial
