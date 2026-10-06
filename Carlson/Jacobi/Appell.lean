/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import Carlson.Jacobi.EndpointBridge
public import Carlson.RPolynomial.Appell

/-!
# Jacobi polynomials as Appell sequences

Carlson (1970), Example 11 and the discussion after Theorem 4: with both parameters lowered by
the degree, the Jacobi polynomials form an Appell sequence. In Carlson's monic endpoint
normalization, `jacobiOn (α - n) (β - n) r s n` equals the two-node R-polynomial
`Rₙ(-α, -β; x - r, x - s)`, and merging the two variables (Theorem 4, `Appell.IsAppell.
comp_reindex_add`) turns the binomial theorem of the R-polynomials into one for the Jacobi
polynomials.

## Main results

* `Carlson.TwoVariable.isAppell_jacobiOn_sub`: `n ↦ jacobiOn (α - n) (β - n) r s n` satisfies
  the binomial theorem `Pₙ(x + λ) = ∑ₘ (n choose m) λ^(n-m) Pₘ(x)` if `α + β` is not a
  nonnegative integer.

## References

* B. C. Carlson, *Polynomials satisfying a binomial theorem*, J. Math. Anal. Appl. 32 (1970),
  543–558, Example 11 and (3.5).
-/

@[expose] public noncomputable section

open Polynomial

namespace Carlson.TwoVariable

/-- [Carl70], Example 11: if `α + β` is not a nonnegative integer, the monic Jacobi
polynomials `jacobiOn (α - n) (β - n) r s n` form an Appell sequence in one variable. -/
theorem isAppell_jacobiOn_sub (α β r s : ℂ) (h : ∀ m : ℕ, α + β ≠ m) :
    Appell.IsAppell fun n (z : Unit → ℂ) => (jacobiOn (α - n) (β - n) r s n).eval (z ()) := by
  have hb : ∀ m : ℕ, ∑ i, pair (-α) (-β) i ≠ -m := by
    intro m hm
    rw [sum_pair] at hm
    exact h m (by linear_combination -hm)
  have key := (isAppell_carlsonRPolynomialNumerator_div hb).comp_reindex_add
    (fun _ : Fin 2 => ()) (pair (-r) (-s))
  have heq : (fun (n : ℕ) (z : Unit → ℂ) => (jacobiOn (α - n) (β - n) r s n).eval (z ())) =
      fun (n : ℕ) (z : Unit → ℂ) => carlsonRPolynomialNumerator n (pair (-α) (-β))
        (fun i => z () + pair (-r) (-s) i) /
          (ascPochhammer ℂ n).eval (∑ i, pair (-α) (-β) i) := by
    funext n z
    have hpoch : (ascPochhammer ℂ n).eval (α - n + (β - n) + n + 1) ≠ 0 := by
      rw [Ne, ascPochhammer_eval_eq_zero_iff]
      rintro ⟨k, hk, hk'⟩
      apply h (n - 1 - k)
      rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
      push_cast
      linear_combination hk'
    have hz : (fun i => z () + pair (-r) (-s) i) = pair (z () - r) (z () - s) := by
      funext i; fin_cases i <;> simp [pair, sub_eq_add_neg]
    rw [eval_jacobiOn_eq_numerator _ _ r s _ n hpoch, hz, carlsonRPolynomialNumerator_pair,
      sum_pair]
    congr 2 <;> ring
  rw [heq]
  exact key

end Carlson.TwoVariable
