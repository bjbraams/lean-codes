/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.DifferentialEquation
public import Carlson.Jacobi.Basis

/-!
# Algebraic beta averages of polynomials

The beta average sends `X^n` to `(a)ₙ / (a+b)ₙ`. This defines a linear
functional over a characteristic-zero field. Its Pearson identity and its
action on shifted Jacobi polynomials require only that the total parameter
avoid the nonpositive integers, rather than positivity of either parameter.

## Main results

* `betaAverage_pearson`: the beta functional annihilates the Pearson operator.
* `betaAverage_shiftedJacobi`: the mean of a positive-degree shifted Jacobi
  polynomial vanishes at every admissible parameter pair.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press,
  1977, §§7.1–7.2.
-/

@[expose] public noncomputable section
namespace Polynomial
variable {K : Type*} [Field K]

/-- The algebraic beta average, defined by its Pochhammer moments. At exceptional
total parameters the quotients are totalized; identities state admissibility separately. -/
def betaAverage (a b : K) : K[X] →ₗ[K] K :=
  lsum (fun n => LinearMap.mulRight K
    ((ascPochhammer K n).eval a / (ascPochhammer K n).eval (a + b)))

/-- The beta average of a monomial is its coefficient times the beta moment. -/
@[simp] theorem betaAverage_monomial (a b c : K) (n : ℕ) :
    betaAverage a b (monomial n c) =
      c * ((ascPochhammer K n).eval a / (ascPochhammer K n).eval (a + b)) := by
  simp [betaAverage, lsum_apply, sum_monomial_index]

/-- The beta average preserves constants. -/
@[simp] theorem betaAverage_C (a b c : K) : betaAverage a b (C c) = c := by
  simpa using betaAverage_monomial a b c 0

/-- Evaluation on a scalar multiple of a power. -/
theorem betaAverage_C_mul_X_pow (a b c : K) (n : ℕ) :
    betaAverage a b (C c * X ^ n) =
      c * ((ascPochhammer K n).eval a / (ascPochhammer K n).eval (a + b)) := by
  rw [C_mul_X_pow_eq_monomial, betaAverage_monomial]

/-- Avoiding the nonpositive integers makes every rising factorial nonzero. -/
theorem ascPochhammer_ne_zero_of_add_nat_ne_zero (c : K)
    (hc : ∀ n : ℕ, c + n ≠ 0) (n : ℕ) : (ascPochhammer K n).eval c ≠ 0 := by
  induction n with
  | zero => simp
  | succ n ih => rw [ascPochhammer_succ_eval]; exact mul_ne_zero ih (hc n)

/-- Adjacent beta moments satisfy the Pearson recurrence. -/
theorem betaAverage_moment_succ (a b : K) (hc : ∀ n : ℕ, a + b + n ≠ 0) (n : ℕ) :
    (a + b + n) * ((ascPochhammer K (n + 1)).eval a /
      (ascPochhammer K (n + 1)).eval (a + b)) =
    (a + n) * ((ascPochhammer K n).eval a / (ascPochhammer K n).eval (a + b)) := by
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval]
  field_simp [hc n, ascPochhammer_ne_zero_of_add_nat_ne_zero (a + b) hc n]

/-- The algebraic beta functional annihilates the first-order Pearson operator. -/
theorem betaAverage_pearson (a b : K) (hc : ∀ n : ℕ, a + b + n ≠ 0) (p : K[X]) :
    betaAverage a b (X * (1 - X) * derivative p + (C a - C (a + b) * X) * p) = 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [mul_add, map_add] at hp hq ⊢
    linear_combination hp + hq
  | monomial n c =>
    have hm := betaAverage_moment_succ a b hc n
    cases n with
    | zero =>
      simp only [monomial_zero_left, derivative_C, mul_zero, zero_add, sub_mul]
      rw [show C (a + b) * X * C c = C ((a + b) * c) * X ^ 1 by simp; ring]
      simp only [← C_mul, betaAverage_C, map_sub, betaAverage_C_mul_X_pow]
      simp only [Nat.cast_zero, add_zero, ascPochhammer_zero, eval_one, div_one] at hm
      linear_combination -c * hm
    | succ n =>
      rw [derivative_monomial_succ]
      simp only [← C_mul_X_pow_eq_monomial]
      rw [show X * (1 - X) * (C (c * (n + 1 : K)) * X ^ n) +
          (C a - C (a + b) * X) * (C c * X ^ (n + 1)) =
          C (c * (a + (n + 1))) * X ^ (n + 1) -
            C (c * (a + b + (n + 1))) * X ^ (n + 1 + 1) by
        simp only [C_mul, C_add, C_eq_natCast]; ring]
      rw [map_sub, betaAverage_C_mul_X_pow, betaAverage_C_mul_X_pow]
      push_cast at hm ⊢
      linear_combination -c * hm

variable [CharZero K]

/-- The shifted Jacobi polynomial has beta mean zero in positive degree and mean one
in degree zero. Only the total beta parameter is restricted. -/
theorem betaAverage_shiftedJacobi (α β : K)
    (hc : ∀ k : ℕ, α + β + 2 + k ≠ 0) (n : ℕ) :
    betaAverage (α + 1) (β + 1) (shiftedJacobi α β n) = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simpa only [shiftedJacobi_zero, C_1, ↓reduceIte] using betaAverage_C (α + 1) (β + 1) 1
  | succ n =>
    have hp := betaAverage_pearson (α + 1) (β + 1)
      (by intro k; convert hc k using 1; ring) (derivative (shiftedJacobi α β (n + 1)))
    have he := congrArg (betaAverage (α + 1) (β + 1))
      (shiftedJacobi_differential_equation α β (n + 1))
    rw [show α + 1 + (β + 1) = α + β + 2 by ring] at hp
    rw [map_add, hp, zero_add, ← smul_eq_C_mul, map_smul, map_zero] at he
    have hn : (n + 1 : K) * ((n + 1) + α + β + 1) ≠ 0 :=
      mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero n)
        (by convert hc n using 1; ring)
    push_cast at he
    simpa only [Nat.succ_ne_zero, ↓reduceIte] using (mul_eq_zero.mp he).resolve_left hn

end Polynomial
