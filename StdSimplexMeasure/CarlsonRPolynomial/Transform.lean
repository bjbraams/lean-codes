/- Copyright (c) 2026 Bastiaan J Braams. All rights reserved. -/
import StdSimplexMeasure.CarlsonRPolynomial.Binomial

/-!
# Linear transformations of Carlson's R-polynomials

This file contains the algebraic infrastructure for [Carl77, Section 6.5].
-/

open Complex
open scoped Classical
public noncomputable section CarlsonRPolynomial
namespace DirichletTransform
variable {ι : Type*} [Fintype ι]

/-- Splitting an ascending Pochhammer symbol and reflecting the remaining factors.

This is the cancellation identity used in Carlson's proof of the linear transformation
6.5-1.  Its multiplicative formulation remains valid when one of the Pochhammer factors
vanishes, unlike the corresponding quotient identity. -/
theorem ascPochhammer_eval_split_reflection (c : ℂ) {m n : ℕ} (hmn : m ≤ n) :
    (ascPochhammer ℂ n).eval c =
      (-1 : ℂ) ^ (n - m) * (ascPochhammer ℂ m).eval c *
        (ascPochhammer ℂ (n - m)).eval (1 - c - n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
  simp only [Nat.add_sub_cancel_left]
  have hmul := congrArg (Polynomial.eval c) (ascPochhammer_mul ℂ m d)
  simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast] at hmul
  rw [← hmul]
  have href := ascPochhammer_eval_neg_eq_descPochhammer ℂ (c + m + d - 1) d
  rw [descPochhammer_eval_eq_ascPochhammer] at href
  have harg : -(c + (m : ℂ) + d - 1) = 1 - c - (m + d : ℕ) := by
    rw [Nat.cast_add]
    ring
  have harg' : c + (m : ℂ) + d - 1 - d + 1 = c + m := by ring
  rw [harg, harg'] at href
  rw [href]
  ring_nf
  simp

/-- Scaling all Carlson variables scales their degree-`n` polynomial kernel by `a ^ n`. -/
theorem eval_carlsonPowerPolynomial_smul (n : ℕ) (a : ℂ) (z x : ι → ℂ) :
    (carlsonPowerPolynomial n (fun i ↦ a * z i)).eval x =
      a ^ n * (carlsonPowerPolynomial n z).eval x := by
  rw [carlsonPowerPolynomial_smul]
  simp

/- Carlson's parameter-changing transformations 6.5-1 and 6.5-3 will be stated first for
`carlsonRPolynomialNumerator`.  In that normalization they are polynomial identities with no
exceptional-parameter hypotheses.  The remaining proof is the finite multi-index regrouping
that combines `ascPochhammer_eval_add` with `ascPochhammer_eval_split_reflection`. -/

end DirichletTransform
end CarlsonRPolynomial
