/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.GegenbauerAddition
public import Carlson.Jacobi.Recurrence

/-!
# The three-term recurrence of Gegenbauer polynomials

The recurrence `(n + 2) C_{n+2}^ν(x) = 2(ν + n + 1) x C_{n+1}^ν(x) - (2ν + n) Cₙ^ν(x)` for all
complex `ν` and `x`. It is obtained from Carlson's monic Jacobi recurrence (Exercise 7.1-6) with
`α = β = ν - 1/2` and endpoints `∓1` away from the half-integers `ν = -k/2`, and extended to all
`ν` by continuity.

## Main results

* `Carlson.TwoVariable.gegenbauer_three_term`: the three-term recurrence.
* `Carlson.TwoVariable.gegenbauer_christoffel_darboux`: the Christoffel–Darboux formula,
  Exercise 6.7-5.

## References

* B. C. Carlson, *Special Functions of Applied Mathematics*, Academic Press, 1977,
  Exercises 6.7-5 and 7.1-6.
-/

open Complex Polynomial

@[expose] public noncomputable section

namespace Carlson.TwoVariable

/-- The Gegenbauer recurrence away from the half-integers `ν = -k/2`. -/
private theorem gegenbauer_three_term_of_ne (ν x : ℂ) (n : ℕ)
    (hν : ∀ k : ℕ, ν ≠ -(k : ℂ) / 2) :
    ((n : ℂ) + 2) * (gegenbauer ν (n + 2)).eval x =
      2 * (ν + n + 1) * x * (gegenbauer ν (n + 1)).eval x -
        (2 * ν + n) * (gegenbauer ν n).eval x := by
  have h2 (j : ℕ) : 2 * ν + j ≠ 0 := fun h => hν j (by linear_combination h / 2)
  have hP (y : ℂ) (m j : ℕ) (hy : y = 2 * ν + j) : (ascPochhammer ℂ m).eval y ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    exact h2 (j + k) (by push_cast; linear_combination -hy + hk)
  have hPν (m : ℕ) : (ascPochhammer ℂ m).eval ν ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    exact h2 (2 * k) (by push_cast; linear_combination 2 * hk)
  have hPh (m : ℕ) : (ascPochhammer ℂ m).eval (ν + 1 / 2) ≠ 0 := by
    rw [Ne, ascPochhammer_eval_eq_zero_iff]
    rintro ⟨k, -, hk⟩
    exact h2 (2 * k + 1) (by push_cast; linear_combination 2 * hk)
  have hconv (m : ℕ) : (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 m).eval x *
      (2 ^ m * (ascPochhammer ℂ m).eval ν) = (m.factorial : ℂ) * (gegenbauer ν m).eval x := by
    have h := eval_jacobiOn_gegenbauer (ν + 1 / 2) x m
      (by rw [show ν + 1 / 2 - 1 / 2 = ν by ring]; exact hPν m) (hPh m)
    rwa [show ν + 1 / 2 - 1 = ν - 1 / 2 by ring, show ν + 1 / 2 - 1 / 2 = ν by ring] at h
  have hrec := eval_jacobiOn_three_term (ν - 1 / 2) (ν - 1 / 2) (-1) 1 x n
    (hP _ n n (by ring)) (hP _ (n + 1) (n + 1) (by push_cast; ring))
    (hP _ (n + 2) (n + 2) (by push_cast; ring)) (by
      have := h2 (2 * n); push_cast at this; intro h; apply this; linear_combination h)
  have hV : jacobiRecurrenceV (ν - 1 / 2) (ν - 1 / 2) (-1 : ℂ) 1 n = 0 := by
    simp [jacobiRecurrenceV]
  rw [hV, sub_zero] at hrec
  have c0 := hconv n
  have c1 := hconv (n + 1)
  have c2 := hconv (n + 2)
  rw [ascPochhammer_succ_eval] at c1
  rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval] at c2
  simp only [jacobiRecurrenceW] at hrec
  have d0 := hPν n
  have d1 := h2 (2 * n); have d2 := h2 (2 * n + 1); have d3 := h2 (2 * n + 2)
  have d4 := h2 n
  push_cast at d1 d2 d3 d4 c1 c2
  have e1 : ν + n ≠ 0 := fun h => d1 (by linear_combination 2 * h)
  have e2 : ν + n + 1 ≠ 0 := fun h => d3 (by linear_combination 2 * h)
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [Nat.factorial_succ, Nat.factorial_succ] at c2
  rw [Nat.factorial_succ] at c1
  push_cast at c1 c2
  generalize (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 n).eval x = p0 at *
  generalize (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 (n + 1)).eval x = p1 at *
  generalize (jacobiOn (ν - 1 / 2) (ν - 1 / 2) (-1) 1 (n + 2)).eval x = p2 at *
  generalize (ascPochhammer ℂ n).eval ν = P at *
  generalize (gegenbauer ν n).eval x = g0 at *
  generalize (gegenbauer ν (n + 1)).eval x = g1 at *
  generalize (gegenbauer ν (n + 2)).eval x = g2 at *
  generalize (n.factorial : ℂ) = F at *
  subst hrec
  have hg0 : g0 = p0 * (2 ^ n * P) / F := by rw [eq_div_iff hf]; linear_combination -c0
  have hn1 : (n : ℂ) + 1 ≠ 0 := by exact_mod_cast n.succ_ne_zero
  have hn2 : (n : ℂ) + 1 + 1 ≠ 0 := by
    have : (0 : ℝ) < n + 1 + 1 := by positivity
    exact_mod_cast this.ne'
  have hg1 : g1 = p1 * (2 ^ (n + 1) * (P * (ν + n))) / ((n + 1) * F) := by
    rw [eq_div_iff (mul_ne_zero hn1 hf)]; linear_combination -c1
  have hg2 : g2 = (x * p1 - (n + 1) * (ν - 1 / 2 + n + 1) * (ν - 1 / 2 + n + 1) *
      (ν - 1 / 2 + (ν - 1 / 2) + n + 1) * (-1 - 1) ^ 2 /
      ((ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 2) ^ 2 * (ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 1) *
        (ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 3)) * p0) *
      (2 ^ (n + 2) * (P * (ν + n) * (ν + (n + 1)))) / ((n + 1 + 1) * ((n + 1) * F)) := by
    rw [eq_div_iff (mul_ne_zero hn2 (mul_ne_zero hn1 hf))]; linear_combination -c2
  have hW : (n + 1) * (ν - 1 / 2 + n + 1) * (ν - 1 / 2 + n + 1) *
      (ν - 1 / 2 + (ν - 1 / 2) + n + 1) * (-1 - 1 : ℂ) ^ 2 /
      ((ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 2) ^ 2 * (ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 1) *
        (ν - 1 / 2 + (ν - 1 / 2) + 2 * n + 3)) =
      (n + 1) * (2 * ν + n) / (4 * (ν + n) * (ν + n + 1)) := by
    rw [show ν - 1 / 2 + (ν - 1 / 2) + 2 * (n : ℂ) + 2 = 2 * ν + (2 * n + 1) by ring,
      show ν - 1 / 2 + (ν - 1 / 2) + 2 * (n : ℂ) + 1 = 2 * (ν + n) by ring,
      show ν - 1 / 2 + (ν - 1 / 2) + 2 * (n : ℂ) + 3 = 2 * (ν + n + 1) by ring,
      show ν - 1 / 2 + n + 1 = (2 * ν + (2 * n + 1)) / 2 by ring,
      show ν - 1 / 2 + (ν - 1 / 2) + (n : ℂ) + 1 = 2 * ν + n by ring]
    generalize 2 * ν + (2 * (n : ℂ) + 1) = Q at d2 ⊢
    field_simp
    ring
  rw [hW] at hg2
  rw [hg0, hg1, hg2]
  field_simp
  ring

/-- The Gegenbauer value `Cₙ^ν(x)` is continuous in the parameter `ν`. -/
theorem continuous_eval_gegenbauer_param (x : ℂ) (n : ℕ) :
    Continuous fun ν : ℂ => (gegenbauer ν n).eval x := by
  unfold gegenbauer shiftedGegenbauer
  simp only [eval_comp, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]
  fun_prop

/-- **The three-term recurrence of Gegenbauer polynomials**, for all complex `ν` and `x`:
`(n + 2) C_{n+2}^ν(x) = 2(ν + n + 1) x C_{n+1}^ν(x) - (2ν + n) Cₙ^ν(x)`. -/
theorem gegenbauer_three_term (ν x : ℂ) (n : ℕ) :
    ((n : ℂ) + 2) * (gegenbauer ν (n + 2)).eval x =
      2 * (ν + n + 1) * x * (gegenbauer ν (n + 1)).eval x -
        (2 * ν + n) * (gegenbauer ν n).eval x := by
  have hL : Continuous fun ν : ℂ => ((n : ℂ) + 2) * (gegenbauer ν (n + 2)).eval x :=
    continuous_const.mul (continuous_eval_gegenbauer_param x _)
  have hR : Continuous fun ν : ℂ => 2 * (ν + n + 1) * x * (gegenbauer ν (n + 1)).eval x -
      (2 * ν + n) * (gegenbauer ν n).eval x := by
    have := continuous_eval_gegenbauer_param x (n + 1)
    have := continuous_eval_gegenbauer_param x n
    fun_prop
  have hbad : (Set.range fun k : ℕ => -(k : ℂ) / 2).Countable := Set.countable_range _
  have h := hL.ext_on (hbad.dense_compl ℂ) hR fun ν hν =>
    gegenbauer_three_term_of_ne ν x n fun k hk => hν ⟨k, hk.symm⟩
  exact congrFun h ν

/-- **Christoffel–Darboux formula** for Gegenbauer polynomials (Exercise 6.7-5): if
`(2ν)_N ≠ 0`, then with `Cₙ^ν(1) = (2ν)ₙ/n!`,
`2(x - y) ∑_{n ≤ N} (n + ν)/Cₙ^ν(1) Cₙ^ν(x) Cₙ^ν(y) =
(N + 1)/C_N^ν(1) [C_{N+1}^ν(x) C_N^ν(y) - C_N^ν(x) C_{N+1}^ν(y)]`. -/
theorem gegenbauer_christoffel_darboux (ν x y : ℂ) (N : ℕ)
    (hN : (ascPochhammer ℂ N).eval (2 * ν) ≠ 0) :
    2 * (x - y) * ∑ n ∈ Finset.range (N + 1), ((n : ℂ) + ν) / (gegenbauer ν n).eval 1 *
        ((gegenbauer ν n).eval x * (gegenbauer ν n).eval y) =
      ((N : ℂ) + 1) / (gegenbauer ν N).eval 1 *
        ((gegenbauer ν (N + 1)).eval x * (gegenbauer ν N).eval y -
          (gegenbauer ν N).eval x * (gegenbauer ν (N + 1)).eval y) := by
  induction N with
  | zero =>
    simp only [Finset.range_one, Finset.sum_singleton, gegenbauer_zero, eval_one, Nat.cast_zero,
      zero_add, div_one, one_mul, mul_one]
    have h1 (z : ℂ) : (gegenbauer ν 1).eval z = 2 * ν * z := by
      simp [gegenbauer, shiftedGegenbauer, Finset.Nat.antidiagonal_succ]; ring
    rw [h1, h1]; ring
  | succ N ih =>
    have hN' : (ascPochhammer ℂ N).eval (2 * ν) ≠ 0 := by
      intro h0; apply hN; rw [ascPochhammer_succ_eval, h0, zero_mul]
    have h2N : 2 * ν + N ≠ 0 := by
      intro h0; apply hN; rw [ascPochhammer_succ_eval, h0, mul_zero]
    rw [Finset.sum_range_succ, mul_add, ih hN']
    simp only [eval_gegenbauer_one, ascPochhammer_succ_eval (n := N), Nat.factorial_succ]
    have hrx := gegenbauer_three_term ν x N
    have hry := gegenbauer_three_term ν y N
    have hf : (N.factorial : ℂ) ≠ 0 := by exact_mod_cast N.factorial_ne_zero
    have hn1 : (N : ℂ) + 1 ≠ 0 := by exact_mod_cast N.succ_ne_zero
    push_cast
    rw [show N + 1 + 1 = N + 2 from rfl, show ((N : ℂ) + 1 + 1) = N + 2 by ring]
    generalize (gegenbauer ν N).eval x = a0 at *
    generalize (gegenbauer ν (N + 1)).eval x = a1 at *
    generalize (gegenbauer ν (N + 2)).eval x = a2 at *
    generalize (gegenbauer ν N).eval y = b0 at *
    generalize (gegenbauer ν (N + 1)).eval y = b1 at *
    generalize (gegenbauer ν (N + 2)).eval y = b2 at *
    field_simp
    linear_combination -(b1 * hrx - a1 * hry)

end Carlson.TwoVariable
